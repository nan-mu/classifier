//! Fixed pool of Lean-initialized OS threads.
//!
//! Process runtime init runs once. Each worker calls `lean_initialize_thread`
//! so up to [`LEAN_WORKERS`] FFI calls can execute in parallel. Job closures
//! must create and free all Lean objects on the same worker thread.

use std::sync::mpsc::{self, Receiver, SyncSender};
use std::sync::{Arc, Mutex, OnceLock};
use std::thread;

use crate::ffi;
use crate::init;

/// Concurrent Lean worker threads (matches server inference permits).
pub const LEAN_WORKERS: usize = 10;

type Job = Box<dyn FnOnce() + Send + 'static>;

struct Pool {
    tx: SyncSender<Job>,
}

static POOL: OnceLock<Pool> = OnceLock::new();

fn ensure_pool() -> &'static Pool {
    POOL.get_or_init(|| {
        init();
        let (tx, rx) = mpsc::sync_channel::<Job>(LEAN_WORKERS);
        let rx = Arc::new(Mutex::new(rx));
        for id in 0..LEAN_WORKERS {
            let rx = Arc::clone(&rx);
            thread::Builder::new()
                .name(format!("lean-worker-{id}"))
                .spawn(move || worker_loop(rx))
                .expect("spawn lean worker");
        }
        Pool { tx }
    })
}

fn worker_loop(rx: Arc<Mutex<Receiver<Job>>>) {
    unsafe {
        ffi::lean_initialize_thread();
    }
    loop {
        let job = {
            let guard = rx.lock().expect("lean worker recv lock");
            guard.recv()
        };
        match job {
            Ok(job) => job(),
            Err(_) => break,
        }
    }
    unsafe {
        ffi::lean_finalize_thread();
    }
}

/// Run `f` on a Lean-initialized worker thread. Blocks the caller until done.
pub fn lean_call<F, T>(f: F) -> T
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    let (reply_tx, reply_rx) = mpsc::sync_channel(0);
    ensure_pool()
        .tx
        .send(Box::new(move || {
            let _ = reply_tx.send(f());
        }))
        .expect("lean worker queue");
    reply_rx.recv().expect("lean worker reply")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ffi;
    use std::sync::{Arc, Barrier};
    use std::time::{Duration, Instant};

    #[test]
    fn ten_workers_overlap_inside_lean_calls() {
        // A global Lean mutex would deadlock: each job waits for all ten to enter.
        let barrier = Arc::new(Barrier::new(LEAN_WORKERS));
        let t0 = Instant::now();
        let mut handles = Vec::new();
        for _ in 0..LEAN_WORKERS {
            let barrier = Arc::clone(&barrier);
            handles.push(thread::spawn(move || {
                lean_call(move || {
                    barrier.wait();
                    unsafe { ffi::classifier_expr_add32(3, 4) }
                })
            }));
        }
        for h in handles {
            assert_eq!(h.join().expect("join"), 7);
        }
        assert!(t0.elapsed() < Duration::from_secs(5));
    }
}
