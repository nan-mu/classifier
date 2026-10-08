//! Root helpers. `cargo xtask demo` starts Lean-backed debug_server + Vite UI.

use std::env;
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

fn main() {
    let mut args = env::args().skip(1);
    let cmd = args.next().unwrap_or_else(|| "demo".into());
    let root = workspace_root();

    match cmd.as_str() {
        "demo" | "run" | "start" => demo(&root),
        "help" | "-h" | "--help" => print_help(),
        other => {
            eprintln!("unknown xtask `{other}`");
            print_help();
            std::process::exit(2);
        }
    }
}

fn print_help() {
    eprintln!(
        "\
cargo xtask <cmd>

  demo   (default)  start debug_server :8788 and debug_web :5173
  help              show this text

One-shot demo:
  cargo xtask
  cargo xtask demo
"
    );
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("xtask lives under repo root")
        .to_path_buf()
}

fn demo(root: &Path) {
    let port = env::var("PORT").unwrap_or_else(|_| "8788".into());
    let host = format!("127.0.0.1:{port}");

    eprintln!("building Lean CommonMath (lake)…");
    run_checked(
        Command::new("lake")
            .args(["build", "CommonMath"])
            .current_dir(root),
        "lake build CommonMath",
    );

    eprintln!("starting debug_server on http://{host} …");
    let mut server = Command::new("cargo")
        .args(["run", "-p", "debug_server"])
        .env("PORT", &port)
        .current_dir(root)
        .stdin(Stdio::null())
        .spawn()
        .unwrap_or_else(|e| panic!("spawn debug_server: {e}"));

    if !wait_tcp(&host, Duration::from_secs(180)) {
        let _ = server.kill();
        panic!("debug_server did not listen on {host}");
    }
    eprintln!("debug_server ready");

    let web = root.join("debug_web");
    eprintln!("npm install (debug_web)…");
    run_checked(
        Command::new("npm").arg("install").current_dir(&web),
        "npm install",
    );

    eprintln!("starting Vite on http://127.0.0.1:5173 …");
    let mut vite = Command::new("npm")
        .args(["run", "dev", "--", "--host", "127.0.0.1", "--port", "5173"])
        .current_dir(&web)
        .stdin(Stdio::null())
        .spawn()
        .unwrap_or_else(|e| panic!("spawn vite: {e}"));

    eprintln!();
    eprintln!("demo up");
    eprintln!("  UI     http://127.0.0.1:5173");
    eprintln!("  API    http://{host}");
    eprintln!("  stop   Ctrl-C");
    eprintln!();

    let stop = Arc::new(AtomicBool::new(false));
    {
        let stop = Arc::clone(&stop);
        ctrlc::set_handler(move || {
            stop.store(true, Ordering::SeqCst);
        })
        .expect("ctrlc handler");
    }

    while !stop.load(Ordering::SeqCst) {
        if child_exited(&mut server) {
            stop_all(&mut vite, &mut server);
            panic!("debug_server exited early");
        }
        if child_exited(&mut vite) {
            stop_all(&mut vite, &mut server);
            panic!("vite exited early");
        }
        thread::sleep(Duration::from_millis(200));
    }

    stop_all(&mut vite, &mut server);
    eprintln!("demo stopped");
}

fn stop_all(vite: &mut Child, server: &mut Child) {
    kill_tree(vite);
    kill_tree(server);
}

fn kill_tree(child: &mut Child) {
    let pid = child.id();
    #[cfg(unix)]
    {
        // Kill the process group leader's children via pkill -P, then the child.
        let _ = Command::new("pkill")
            .args(["-P", &pid.to_string()])
            .status();
    }
    let _ = child.kill();
    let _ = child.wait();
}

fn run_checked(cmd: &mut Command, label: &str) {
    let status = cmd.status().unwrap_or_else(|e| panic!("{label}: {e}"));
    if !status.success() {
        panic!("{label} failed with {status}");
    }
}

fn wait_tcp(addr: &str, budget: Duration) -> bool {
    let start = Instant::now();
    while start.elapsed() < budget {
        if TcpStream::connect(addr).is_ok() {
            return true;
        }
        thread::sleep(Duration::from_millis(200));
    }
    false
}

fn child_exited(child: &mut Child) -> bool {
    match child.try_wait() {
        Ok(Some(_)) => true,
        Ok(None) => false,
        Err(_) => true,
    }
}
