use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use classifier::rv32::Environment;
use classifier::{
    Arch, DEFAULT_COQQFBV, QfbvQuery, QfbvStatus, check_qfbv_file_with,
    compile_xdp_bpf_path_asserts, compile_xdp_rv32_path_asserts,
    discover_path_family_matching_with, pathgen_bpf, pathgen_rv32, prefixgen_bpf_object,
    prefixgen_rv32_elf, verify_path_family_matching_with, write_path_family_evidence,
    write_pathgen, write_prefixgen, xdp_environment_contract,
};

const DEFAULT_BPF_OBJECT: &str = "example/bpf.o";
const DEFAULT_RV32_ELF: &str = "example/just_tx.elf";
const DEFAULT_RV32_ENVIRONMENT: &str = "config/esp32c3.environment.toml";
const DEFAULT_OUT: &str = "out";
const DEFAULT_EQUIV_OUT: &str = "out/qfbv/xdp-assert-equiv";

fn resolve(path: impl AsRef<Path>) -> PathBuf {
    let path = path.as_ref();
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        Path::new(env!("CARGO_MANIFEST_DIR")).join(path)
    }
}

#[derive(Parser, Debug)]
#[command(
    name = "classifier",
    about = "BPF / RV32IMC prefixgen + pathgen and QF_BV checking"
)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Generate BPF Prefix + paths from `bpf.o` under `out/bpf/`.
    #[command(name = "bpf", alias = "bpf-prefixgen")]
    Bpf {
        #[arg(default_value = DEFAULT_BPF_OBJECT)]
        input: PathBuf,
        #[arg(short, long, default_value = DEFAULT_OUT)]
        output: PathBuf,
    },
    /// Generate RV32IMC Prefix + paths from xpost ELF under `out/rv32imc/`.
    #[command(name = "rv32", alias = "rv32-prefixgen")]
    Rv32 {
        #[arg(long, default_value = DEFAULT_RV32_ELF)]
        elf: PathBuf,
        #[arg(long, default_value = DEFAULT_RV32_ENVIRONMENT)]
        environment: PathBuf,
        #[arg(short, long, default_value = DEFAULT_OUT)]
        output: PathBuf,
    },
    /// Check an SMT-LIB2 QF_BV file with standalone CoqQFBV.
    Qfbv {
        input: PathBuf,
        #[arg(long, default_value = DEFAULT_COQQFBV)]
        solver: PathBuf,
        #[arg(long)]
        split_conjs: bool,
    },
    /// Match and verify BPF/RV32 XDP path assertion behavior with QF_BV.
    XdpAssertEquiv {
        #[arg(long, default_value = DEFAULT_BPF_OBJECT)]
        bpf: PathBuf,
        #[arg(long, default_value = DEFAULT_RV32_ELF)]
        rv32: PathBuf,
        #[arg(long, default_value = DEFAULT_RV32_ENVIRONMENT)]
        environment: PathBuf,
        #[arg(short, long, default_value = DEFAULT_EQUIV_OUT)]
        output: PathBuf,
        /// Authoritative verification backend; use standalone CoqQFBV.
        #[arg(long, default_value = DEFAULT_COQQFBV)]
        solver: PathBuf,
        /// Optional untrusted backend used only to discover candidate pairs.
        #[arg(long)]
        oracle: Option<PathBuf>,
        #[arg(long)]
        split_conjs: bool,
    },
}

fn run_bpf(input: &Path, output: &Path) -> Result<()> {
    let input = resolve(input);
    let output = resolve(output);
    let insns = prefixgen_bpf_object(&input)?;
    let prog = write_prefixgen(&output, Arch::Bpf, &insns)?;
    eprintln!("wrote {} BPF insns to {}", insns.len(), prog.display());
    let paths = pathgen_bpf(&insns)?;
    let path_dir = write_pathgen(&output, Arch::Bpf, &paths)?;
    eprintln!("wrote {} BPF paths to {}", paths.len(), path_dir.display());
    Ok(())
}

fn run_rv32(elf: &Path, environment: &Path, output: &Path) -> Result<()> {
    let elf = resolve(elf);
    let environment = resolve(environment);
    let output = resolve(output);
    let env = Environment::from_toml(
        &std::fs::read_to_string(&environment)
            .with_context(|| format!("read environment {}", environment.display()))?,
    )?;
    let insns = prefixgen_rv32_elf(&elf, &env)?;
    let prog = write_prefixgen(&output, Arch::Rv32imc, &insns)?;
    eprintln!("wrote {} RV32IMC insns to {}", insns.len(), prog.display());
    let paths = pathgen_rv32(&insns, &env)?;
    let path_dir = write_pathgen(&output, Arch::Rv32imc, &paths)?;
    eprintln!(
        "wrote {} RV32IMC paths to {}",
        paths.len(),
        path_dir.display()
    );
    Ok(())
}

fn check_query(
    query: &QfbvQuery,
    query_path: &Path,
    executable: &Path,
    split_conjs: bool,
) -> Result<QfbvStatus> {
    query.write_smt2(query_path)?;
    check_qfbv_file_with(executable, query_path, split_conjs)
}

fn run_xdp_assert_equiv(
    bpf: &Path,
    rv32: &Path,
    environment: &Path,
    output: &Path,
    solver: &Path,
    oracle: Option<&Path>,
    split_conjs: bool,
) -> Result<()> {
    let bpf = resolve(bpf);
    let rv32 = resolve(rv32);
    let environment_path = resolve(environment);
    let output = resolve(output);
    let environment = Environment::from_toml(
        &std::fs::read_to_string(&environment_path)
            .with_context(|| format!("read environment {}", environment_path.display()))?,
    )?;
    std::fs::create_dir_all(&output)?;
    std::fs::write(
        output.join("manifest.txt"),
        "format=classifier-xdp-assert-equivalence-v1\nstatus=incomplete\n",
    )?;

    let bpf_program = prefixgen_bpf_object(&bpf)?;
    let rv32_program = prefixgen_rv32_elf(&rv32, &environment)?;
    let bpf_paths = pathgen_bpf(&bpf_program)?;
    let rv32_paths = pathgen_rv32(&rv32_program, &environment)?;
    let left = bpf_paths
        .iter()
        .map(|path| compile_xdp_bpf_path_asserts(path, &environment))
        .collect::<std::result::Result<Vec<_>, _>>()?;
    let right = rv32_paths
        .iter()
        .map(|path| compile_xdp_rv32_path_asserts(path, &environment))
        .collect::<std::result::Result<Vec<_>, _>>()?;
    let contract = xdp_environment_contract(&environment)?;
    let query_path = std::env::temp_dir().join(format!(
        "classifier-xdp-assert-equiv-{}.smt2",
        std::process::id()
    ));
    let discovery_backend = oracle.unwrap_or(solver);
    let discovery_split = oracle.is_none() && split_conjs;

    let result = (|| {
        let matching = discover_path_family_matching_with(&left, &right, &contract, |query| {
            check_query(query, &query_path, discovery_backend, discovery_split)
        })?;
        let evidence =
            verify_path_family_matching_with(&left, &right, &contract, matching, |query| {
                check_query(query, &query_path, solver, split_conjs)
            })?;
        let inputs = output.join("inputs");
        write_prefixgen(&inputs, Arch::Bpf, &bpf_program)?;
        write_pathgen(&inputs, Arch::Bpf, &bpf_paths)?;
        write_prefixgen(&inputs, Arch::Rv32imc, &rv32_program)?;
        write_pathgen(&inputs, Arch::Rv32imc, &rv32_paths)?;
        let manifest = write_path_family_evidence(
            &output,
            &left,
            &right,
            &contract,
            &evidence,
            &discovery_backend.to_string_lossy(),
            &solver.to_string_lossy(),
        )?;
        eprintln!(
            "verified {} path pairs after checking {} candidates; evidence: {}",
            evidence.matching().pairs.len(),
            evidence.matching().checked_pairs,
            manifest.display()
        );
        Ok(())
    })();
    let _ = std::fs::remove_file(query_path);
    result
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        None => {
            run_rv32(
                Path::new(DEFAULT_RV32_ELF),
                Path::new(DEFAULT_RV32_ENVIRONMENT),
                Path::new(DEFAULT_OUT),
            )?;
            run_bpf(Path::new(DEFAULT_BPF_OBJECT), Path::new(DEFAULT_OUT))?;
            Ok(())
        }
        Some(Command::Bpf { input, output }) => run_bpf(&input, &output),
        Some(Command::Rv32 {
            elf,
            environment,
            output,
        }) => run_rv32(&elf, &environment, &output),
        Some(Command::Qfbv {
            input,
            solver,
            split_conjs,
        }) => {
            let status = check_qfbv_file_with(solver, resolve(input), split_conjs)?;
            println!("{status}");
            Ok(())
        }
        Some(Command::XdpAssertEquiv {
            bpf,
            rv32,
            environment,
            output,
            solver,
            oracle,
            split_conjs,
        }) => run_xdp_assert_equiv(
            &bpf,
            &rv32,
            &environment,
            &output,
            &solver,
            oracle.as_deref(),
            split_conjs,
        ),
    }
}
