//! The in-process modeller's two environment switches, end to end (task
//! #97-FLAGS-TEST).  `con-ron --help` promises (`src/bin/con-ron.rs`, the
//! `environment (con-leche's):` paragraph):
//!
//! * `CON_LECHE_INMODEL=0` turns the modeller off, so a mutual or nested
//!   block is pushed bare and the fold DECLINES it, having found no route;
//! * `CON_LECHE_INMODEL_CENSUS=1` reports every mutual/nested block's
//!   outcome after the parse and stops with exit 2.
//!
//! Both runs are outside the theorem (OVERVIEW.md §3.1), so nothing but this
//! test checks that the switches still do what the help text says.
//!
//! The fixture `fixtures/ind_mutual_sort_defeq.ndjson` is a verbatim copy
//! (7.6 KB) of con-leche's `tests/e2e/ind_mutual_sort_defeq.ndjson` at rev
//! 78ded4b6, expectation `0` in its `tests/e2e-expected.txt`: one two-member
//! mutual block `MC`.  It is copied rather than read from the con-leche lake
//! package so that `cargo test` does not depend on `lake update` having run.

use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// The run's timeout: the fixture takes ~25 ms.
const TIMEOUT: Duration = Duration::from_secs(60);

/// Run the binary on the fixture with `--jobs=1` and the given environment
/// (both switches cleared first, so an inherited one cannot leak in), and
/// return (exit code, stdout, stderr).
fn run(env: &[(&str, &str)]) -> (i32, String, String) {
    let fixture: PathBuf = [
        env!("CARGO_MANIFEST_DIR"),
        "tests",
        "fixtures",
        "ind_mutual_sort_defeq.ndjson",
    ]
    .iter()
    .collect();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_con-ron"));
    cmd.arg("--jobs=1")
        .arg(&fixture)
        .env_remove("CON_LECHE_INMODEL")
        .env_remove("CON_LECHE_INMODEL_CENSUS")
        .env_remove("CON_LECHE_PROJREC_TRACE")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for (k, v) in env {
        cmd.env(k, v);
    }
    let mut child = cmd.spawn().expect("spawn con-ron");
    let start = Instant::now();
    while child.try_wait().expect("wait for con-ron").is_none() {
        if start.elapsed() > TIMEOUT {
            let _ = child.kill();
            panic!("con-ron {env:?} timed out after {TIMEOUT:?}");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let out = child.wait_with_output().expect("collect con-ron output");
    let code = out.status.code().expect("con-ron killed by a signal");
    (
        code,
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

#[test]
fn default_flags_accept() {
    let (code, out, err) = run(&[]);
    assert_eq!(code, 0, "stdout:\n{out}\nstderr:\n{err}");
    assert!(err.contains("1 inductive blocks modelled in-process: MC"), "{err}");
    // The verdict line is on stdout, the modeller's report on stderr.
    assert!(out.contains("accepted 3 declarations (--verified)"), "{out}");
}

#[test]
fn inmodel_off_declines_with_no_route() {
    let (code, out, err) = run(&[("CON_LECHE_INMODEL", "0")]);
    assert_eq!(code, 2, "stdout:\n{out}\nstderr:\n{err}");
    assert!(err.contains("declined: no install route for inductive block"), "{err}");
    assert!(err.contains("[at inductive MC,"), "{err}");
    assert!(!err.contains("modelled in-process"), "{err}");
}

#[test]
fn census_reports_and_stops() {
    let (code, out, err) = run(&[("CON_LECHE_INMODEL_CENSUS", "1")]);
    assert_eq!(code, 2, "stdout:\n{out}\nstderr:\n{err}");
    assert!(err.contains("inmodel census: 1 modelled, 0 declined"), "{err}");
    assert!(err.contains("parse only"), "{err}");
    assert!(!out.contains("accepted") && !err.contains("accepted"), "{out}{err}");
}
