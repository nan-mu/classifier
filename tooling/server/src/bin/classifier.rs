//! JSON CLI over `server::Kernel`. Exit 0 ok, 1 domain error, 2 usage.

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;

use serde_json::Value;
use server::api::{snap_run_from_snapshot, Command, Envelope, ImageSource, Kernel};
use server::expand::Arch;
use server::harness;
use server::KernelError;

fn main() -> ExitCode {
    let mut args = env::args().skip(1).collect::<Vec<_>>();
    if args.is_empty() {
        usage();
        return emit(usage_err("usage", "missing command"));
    }
    let cmd = args.remove(0);
    let kernel = Kernel::new();
    match cmd.as_str() {
        "create" => emit(do_create(&kernel, &args)),
        "run" => emit(do_run(&kernel, &args)),
        "get" => emit(do_get(&kernel, &args)),
        "compare-tree" => emit(do_compare_tree(&kernel, &args)),
        "exec" => emit(do_exec(&kernel)),
        "test" => run_test(&args),
        "-h" | "--help" | "help" => {
            usage();
            emit(usage_err("usage", "help"))
        }
        _ => {
            usage();
            emit(usage_err("usage", format!("unknown command {cmd}")))
        }
    }
}

fn usage() {
    eprintln!(
        "classifier create --arch ARCH --budget N [--image PATH] [--map-elf PATH] [--name N]\n\
         classifier run --session ID\n\
         classifier get --session ID\n\
         classifier compare-tree --left PATH.json --right PATH.json\n\
         classifier exec   # one Command-shaped JSON on stdin (see docs)\n\
         classifier test --root DIR\n\
         stdout: one Envelope JSON; exit 0 ok, 1 error, 2 usage"
    );
}

fn emit(env: Envelope) -> ExitCode {
    match serde_json::to_string(&env) {
        Ok(s) => println!("{s}"),
        Err(e) => {
            eprintln!("serialize: {e}");
            return ExitCode::from(1);
        }
    }
    if env.ok {
        ExitCode::SUCCESS
    } else if env.error.as_ref().map(|e| e.code.as_str()) == Some("usage") {
        ExitCode::from(2)
    } else {
        ExitCode::from(1)
    }
}

fn flag<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    let mut i = 0;
    while i < args.len() {
        if args[i] == name {
            return args.get(i + 1).map(|s| s.as_str());
        }
        i += 1;
    }
    None
}

fn do_create(kernel: &Kernel, args: &[String]) -> Envelope {
    let arch = match Arch::parse(flag(args, "--arch").unwrap_or("rv32imc")) {
        Some(a) => a,
        None => return usage_err("create", "bad --arch"),
    };
    let budget: u32 = flag(args, "--budget")
        .unwrap_or("1024")
        .parse()
        .unwrap_or(1024);
    let image = match flag(args, "--image") {
        None => ImageSource::Default,
        Some(p) => ImageSource::Path(PathBuf::from(p)),
    };
    let map_elf = flag(args, "--map-elf").map(|p| ImageSource::Path(PathBuf::from(p)));
    let name = flag(args, "--name").map(|s| s.to_string());
    kernel.execute(Command::Create {
        arch,
        budget,
        name,
        image,
        map_elf,
    })
}

fn do_run(kernel: &Kernel, args: &[String]) -> Envelope {
    let Some(id) = flag(args, "--session") else {
        return usage_err("run", "missing --session");
    };
    kernel.execute(Command::Run {
        session_id: id.into(),
    })
}

fn do_get(kernel: &Kernel, args: &[String]) -> Envelope {
    let Some(id) = flag(args, "--session") else {
        return usage_err("get", "missing --session");
    };
    kernel.execute(Command::Get {
        session_id: id.into(),
    })
}

fn do_compare_tree(kernel: &Kernel, args: &[String]) -> Envelope {
    let Some(left_p) = flag(args, "--left") else {
        return usage_err("compare-tree", "missing --left");
    };
    let Some(right_p) = flag(args, "--right") else {
        return usage_err("compare-tree", "missing --right");
    };
    let left = match read_json(left_p) {
        Ok(v) => normalize_snap_run(v),
        Err(e) => return usage_err("compare-tree", e),
    };
    let right = match read_json(right_p) {
        Ok(v) => normalize_snap_run(v),
        Err(e) => return usage_err("compare-tree", e),
    };
    kernel.execute(Command::CompareTree { left, right })
}

fn normalize_snap_run(v: Value) -> Value {
    if v.get("nodes").is_some() && v.get("arch").is_some() && v.get("edges").is_some() {
        v
    } else {
        snap_run_from_snapshot(&v)
    }
}

fn read_json(path: &str) -> Result<Value, String> {
    let raw = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    serde_json::from_str(&raw).map_err(|e| e.to_string())
}

fn do_exec(kernel: &Kernel) -> Envelope {
    let raw = match std::io::read_to_string(std::io::stdin()) {
        Ok(s) => s,
        Err(e) => return usage_err("exec", e.to_string()),
    };
    let v: Value = match serde_json::from_str(&raw) {
        Ok(v) => v,
        Err(e) => return usage_err("exec", e.to_string()),
    };
    let cmd = match parse_exec_command(&v) {
        Ok(c) => c,
        Err(e) => return usage_err("exec", e),
    };
    kernel.execute(cmd)
}

fn parse_exec_command(v: &Value) -> Result<Command, String> {
    let op = v
        .get("op")
        .and_then(|x| x.as_str())
        .ok_or("exec JSON needs op")?;
    match op {
        "create" => {
            let arch = Arch::parse(v.get("arch").and_then(|x| x.as_str()).unwrap_or("rv32imc"))
                .ok_or("bad arch")?;
            let budget = v.get("budget").and_then(|x| x.as_u64()).unwrap_or(1024) as u32;
            let image = match v.get("image").and_then(|x| x.as_str()) {
                None | Some("") => ImageSource::Default,
                Some(p) => ImageSource::Path(PathBuf::from(p)),
            };
            let map_elf = v
                .get("map_elf")
                .and_then(|x| x.as_str())
                .map(|p| ImageSource::Path(PathBuf::from(p)));
            Ok(Command::Create {
                arch,
                budget,
                name: v
                    .get("name")
                    .and_then(|x| x.as_str())
                    .map(|s| s.to_string()),
                image,
                map_elf,
            })
        }
        "run" => Ok(Command::Run {
            session_id: v
                .get("session_id")
                .and_then(|x| x.as_str())
                .ok_or("run needs session_id")?
                .into(),
        }),
        "get" => Ok(Command::Get {
            session_id: v
                .get("session_id")
                .and_then(|x| x.as_str())
                .ok_or("get needs session_id")?
                .into(),
        }),
        "compare_tree" => Ok(Command::CompareTree {
            left: v.get("left").cloned().ok_or("compare_tree needs left")?,
            right: v.get("right").cloned().ok_or("compare_tree needs right")?,
        }),
        other => Err(format!("unknown op {other}")),
    }
}

fn usage_err(command: &str, message: impl Into<String>) -> Envelope {
    Envelope {
        v: 1,
        ok: false,
        command: command.into(),
        session_id: None,
        payload: None,
        error: Some(KernelError {
            code: "usage".into(),
            message: message.into(),
        }),
    }
}

fn run_test(args: &[String]) -> ExitCode {
    let Some(root) = flag(args, "--root") else {
        return emit(usage_err("test", "missing --root"));
    };
    let report = harness::run_suite(&PathBuf::from(root));
    let env = Envelope {
        v: 1,
        ok: report.all_ok(),
        command: "test".into(),
        session_id: None,
        payload: Some(report.to_json()),
        error: if report.all_ok() {
            None
        } else {
            Some(KernelError {
                code: "cases".into(),
                message: "one or more cases failed".into(),
            })
        },
    };
    emit(env)
}
