//! The simple scheduler: `con-ron --olean --schedule` (con-leche's
//! `Driver/Schedule/Run.lean`, its process loop cut down to what a correct run
//! needs).
//!
//! ```text
//! con-ron [OPTIONS] --olean --schedule [--jobs=N] [--schedule-order=ORDER]
//!         [--schedule-timeout=S] [--worker-stack-size=SIZE] --search-path=DIRS [--] MODULE
//! con-ron [OPTIONS] --olean --schedule --compare [--trusted-search-path=DIRS]
//!         --search-path=DIRS [--] CHALLENGE SOLUTION
//! ```
//!
//! After the graph check (`modular::schedule`, in this process), the workers are
//! exactly the `--module` commands `--schedule-commands` prints, each with
//! `--jobs=1`, started as children of this binary (`std::env::current_exe`), at
//! most `--jobs=N` at a time, in the start order; their stdin closed, their stdout
//! dropped, their stderr kept.  Each finished worker is one line on stdout; at
//! the end each failing module's verdict and its last stderr line are written to
//! stderr, then upstream's verdict line (`summary`), with upstream's exit-code
//! rule.
//!
//! Of upstream's scheduler this leaves out the memory budget and its kills, the
//! thread budget (every worker runs one thread), the log and its resumption, the
//! status part of the lines and the heartbeat, the cgroup's OOM-kill counter and
//! the signal handling (an interrupt reaches the workers through the terminal's
//! process group).  `--schedule-log` and `--schedule-memory` are usage errors
//! (`modular::schedule`).  Outside the theorems, as upstream's: the guarantee is
//! that of the commands it runs.

use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant};

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:131-137 signalName
/// The usual signals' names.
fn signal_name(n: i32) -> Option<&'static str> {
    match n {
        1 => Some("SIGHUP"),
        2 => Some("SIGINT"),
        3 => Some("SIGQUIT"),
        4 => Some("SIGILL"),
        6 => Some("SIGABRT"),
        7 => Some("SIGBUS"),
        8 => Some("SIGFPE"),
        9 => Some("SIGKILL"),
        11 => Some("SIGSEGV"),
        13 => Some("SIGPIPE"),
        15 => Some("SIGTERM"),
        _ => None,
    }
}

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:139-152 exitVerdict
/// **A worker's verdict** from how it ended and its stderr `diag`: `0` to `3` as
/// they are, `exit N` for another code; ended by a signal, `stack` (SIGABRT and
/// a stack overflow's message: Lean's, or Rust's), else `signal N (NAME)`.  No
/// `oom-kill`: the cgroup's counter is not read.
pub fn exit_verdict(st: &std::process::ExitStatus, diag: &str) -> String {
    use std::os::unix::process::ExitStatusExt;
    match (st.code(), st.signal()) {
        (Some(c), _) if (0..=3).contains(&c) => c.to_string(),
        (Some(c), _) => format!("exit {}", c),
        (None, Some(s)) => {
            if s == 6 && (diag.contains("Stack overflow detected") || diag.contains("has overflowed its stack")) {
                "stack".to_string()
            } else {
                match signal_name(s) {
                    Some(n) => format!("signal {} ({})", s, n),
                    None => format!("signal {}", s),
                }
            }
        }
        (None, None) => "exit ?".to_string(),
    }
}

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:219-222 passedOn
/// The lines of a worker's stderr worth passing on: all but the empty ones and
/// its statistics.
fn passed_on(msg: &str) -> Vec<&str> {
    msg.lines().filter(|l| !l.is_empty() && !l.contains(": stats:")).collect()
}

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:224-230 stackHint
/// The hint after a `stack` verdict: the stack size the worker ran at.
fn stack_hint(m: &str, stack_kb: Option<u64>) -> String {
    let now = match stack_kb {
        Some(k) => format!("{} KiB", k),
        None => "the inherited one".to_string(),
    };
    format!(
        "con-ron: schedule: {}: the worker overflowed its stack; rerun with a larger \
         --worker-stack-size (now {})",
        m, now
    )
}

/// con-leche: ConLeche/Driver/Schedule/Run.lean:132-142 spawnW
/// **One worker, start to end**: `app` at `args`, `LEAN_STACK_SIZE_KB` set where
/// `stack_kb` is given, stdin closed, stdout read and dropped, stderr read whole;
/// killed after `timeout_s` seconds where that is not 0 (the verdict `timeout`).
/// Its verdict, its stderr, its run time in ms.
fn run_worker(app: &str, args: &[String], stack_kb: Option<u64>, timeout_s: u64) -> (String, String, u128) {
    let t0 = Instant::now();
    let mut cmd = Command::new(app);
    cmd.args(args).stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    if let Some(k) = stack_kb {
        cmd.env("LEAN_STACK_SIZE_KB", k.to_string());
    }
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => return ("3".to_string(), format!("con-ron: schedule: the worker could not be started: {}", e), 0),
    };
    let out = child.stdout.take();
    let err = child.stderr.take();
    let out_t = std::thread::spawn(move || {
        if let Some(mut o) = out {
            let _ = std::io::copy(&mut o, &mut std::io::sink());
        }
    });
    let err_t = std::thread::spawn(move || {
        let mut s = Vec::new();
        if let Some(mut e) = err {
            let _ = e.read_to_end(&mut s);
        }
        String::from_utf8_lossy(&s).into_owned()
    });
    let mut timed_out = false;
    let status = loop {
        if timeout_s == 0 {
            break child.wait();
        }
        match child.try_wait() {
            Ok(Some(st)) => break Ok(st),
            Ok(None) => {
                if timeout_s > 0 && t0.elapsed() > Duration::from_secs(timeout_s) {
                    let _ = child.kill();
                    timed_out = true;
                    break child.wait();
                }
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(e) => break Err(e),
        }
    };
    let _ = out_t.join();
    let diag = err_t.join().unwrap_or_default();
    let ms = t0.elapsed().as_millis();
    match status {
        _ if timed_out => ("timeout".to_string(), diag, ms),
        Ok(st) => {
            let v = exit_verdict(&st, &diag);
            (v, diag, ms)
        }
        Err(e) => ("3".to_string(), format!("con-ron: schedule: the worker could not be waited for: {}", e), ms),
    }
}

/// con-leche: ConLeche/Driver/Schedule/Status.lean:178-186 finishText
/// A finished worker's line: the count so far, its run time, `FAILED <verdict>`
/// where it is not 0, the module.
fn finish_text(done: usize, total: usize, ms: u128, w: &str, m: &str) -> String {
    let mark = if w == "0" { String::new() } else { format!("FAILED {}  ", w) };
    format!("[{}/{}]  t={:>7}s  {}{}", done, total, crate::driver::ms_secs(ms), mark, m)
}

/// con-leche: ConLeche/Driver/Schedule/Run.lean:217-591 run
/// **The workers**: `work[i]` is the module `i` of the start order (its
/// spelling for the lines, its worker's arguments), run by `jobs` threads, each
/// taking the next unstarted module.  Each one's verdict and stderr, by index.
pub fn run(app: &str, work: &[(String, Vec<String>)], jobs: u64, stack_kb: Option<u64>, timeout_s: u64) -> Vec<(String, String)> {
    let total = work.len();
    let mut res: Vec<(String, String)> = vec![(String::new(), String::new()); total];
    let next = AtomicUsize::new(0);
    let (tx, rx) = mpsc::channel::<(usize, String, String, u128)>();
    let n = std::cmp::max(1, std::cmp::min(jobs as usize, total));
    std::thread::scope(|sc| {
        for _ in 0..n {
            let tx = tx.clone();
            let next = &next;
            sc.spawn(move || loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                if i >= total {
                    break;
                }
                let (w, diag, ms) = run_worker(app, &work[i].1, stack_kb, timeout_s);
                if tx.send((i, w, diag, ms)).is_err() {
                    break;
                }
            });
        }
        drop(tx);
        let mut done = 0;
        let out = std::io::stdout();
        for (i, w, diag, ms) in rx {
            done += 1;
            let mut o = out.lock();
            let _ = writeln!(o, "{}", finish_text(done, total, ms, &w, &work[i].0));
            let _ = o.flush();
            res[i] = (w, diag);
        }
    });
    res
}

/// con-leche: ConLeche/Driver/Schedule/Run.lean:593-616 summary
/// **The run's verdict**, the modules `mods` in the graph's order with their
/// verdicts and stderr: each failing one's verdict and last stderr line on
/// stderr (the stack hint after a `stack`), then 0 and the accept line where
/// every worker answered 0; else the first failing module in the graph's order
/// named, and its code (`timeout`, `stack`, `signal …`, `exit N`: 3).
pub fn summary(mods: &[(String, String, String)], mode_tag: &str, stack_kb: Option<u64>) -> u8 {
    let bad: Vec<&(String, String, String)> = mods.iter().filter(|x| x.1 != "0").collect();
    let e = std::io::stderr();
    let mut e = e.lock();
    for (m, w, diag) in &bad {
        match passed_on(diag).last() {
            Some(l) => {
                let _ = writeln!(e, "con-ron: schedule: {}: {}: {}", m, w, l);
            }
            None => {
                let _ = writeln!(e, "con-ron: schedule: {}: {}", m, w);
            }
        }
        if w == "stack" {
            let _ = writeln!(e, "{}", stack_hint(m, stack_kb));
        }
    }
    match bad.first() {
        None => {
            drop(e);
            let mut o = std::io::stdout().lock();
            let _ = writeln!(o, "con-ron: accepted {} modules, one worker each ({})", mods.len(), mode_tag);
            let _ = o.flush();
            0
        }
        Some((m, w, _)) => {
            let _ = writeln!(
                e,
                "con-ron: {} of {} modules not accepted; the first in the graph's order: {} ({}) ({})",
                bad.len(),
                mods.len(),
                m,
                w,
                mode_tag
            );
            match w.as_str() {
                "1" => 1,
                "2" => 2,
                _ => 3,
            }
        }
    }
}
