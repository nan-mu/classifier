use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use classifier::rv32::Environment;
use classifier::{
    pathgen_bpf, pathgen_rv32, write_pathgen, write_prefixgen, Arch, prefixgen_bpf_object,
    prefixgen_rv32_elf,
};

const DEFAULT_BPF_OBJECT: &str = "example/bpf.o";
const DEFAULT_RV32_ELF: &str = "example/just_tx.elf";
const DEFAULT_RV32_ENVIRONMENT: &str = "config/esp32c3.environment.toml";
const DEFAULT_OUT: &str = "out";

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
    about = "BPF / RV32IMC prefixgen + pathgen from ELF machine code"
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
}

fn run_bpf(input: &Path, output: &Path) -> Result<()> {
    let input = resolve(input);
    let output = resolve(output);
    let insns = prefixgen_bpf_object(&input)?;
    let prog = write_prefixgen(&output, Arch::Bpf, &insns)?;
    eprintln!(
        "wrote {} BPF insns to {}",
        insns.len(),
        prog.display()
    );
    let paths = pathgen_bpf(&insns)?;
    let path_dir = write_pathgen(&output, Arch::Bpf, &paths)?;
    eprintln!(
        "wrote {} BPF paths to {}",
        paths.len(),
        path_dir.display()
    );
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
    eprintln!(
        "wrote {} RV32IMC insns to {}",
        insns.len(),
        prog.display()
    );
    let paths = pathgen_rv32(&insns, &env)?;
    let path_dir = write_pathgen(&output, Arch::Rv32imc, &paths)?;
    eprintln!(
        "wrote {} RV32IMC paths to {}",
        paths.len(),
        path_dir.display()
    );
    Ok(())
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
    }
}
