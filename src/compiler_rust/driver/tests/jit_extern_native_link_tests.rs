//! Cranelift JIT: runtime externs registered in `RUNTIME_SYMBOL_NAMES` with an
//! exact `RuntimeFuncSpec` must link natively. `run_file_jit` otherwise
//! rewrites every call into the interpreter bridge and records
//! `[engine-demotion] reason=hybrid-interp-splice detail=<names>`.
//! doc/08_tracking/bug/jit_caret_392_unregistered_externs_hybrid_splice_2026-11-13.md
//!
//! The tests drive the real `simple` binary so they observe the demotion
//! receipt the user sees. `SIMPLE_JIT_EXTERN_TEST_SEED=<path>` points them at
//! another seed binary (used to record the red run against the pre-fix seed).

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

fn seed() -> PathBuf {
    std::env::var_os("SIMPLE_JIT_EXTERN_TEST_SEED")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_simple")))
}

fn write_source(tag: &str, source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("jit_extern_native_link_{}_{tag}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let probe_file = dir.join("probe_target.txt");
    std::fs::write(&probe_file, b"probe").expect("probe target");
    let path = dir.join("main.spl");
    std::fs::write(&path, source.replace("__P__", probe_file.to_str().expect("utf8 temp path"))).expect("source");
    path
}

fn run(path: &PathBuf, interpret: bool, stdin: &[u8]) -> Output {
    let mut command = Command::new(seed());
    command
        .arg("run")
        .arg(path)
        .env("SIMPLE_RUST_SEED_WARNING", "0")
        .env_remove("SIMPLE_EXECUTION_MODE")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if interpret {
        command.env("SIMPLE_EXECUTION_MODE", "interpret");
    }
    let mut child = command.spawn().expect("spawn seed");
    child.stdin.take().expect("stdin").write_all(stdin).expect("write stdin");
    child.wait_with_output().expect("seed output")
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// Externs that also have an interpreter handler: JIT and interpreter must agree.
const INTERP_BACKED: &str = r#"
extern fn rt_file_modified(path: text) -> i64
extern fn rt_file_modified_time(path: text) -> i64
extern fn rt_file_mode(path: text) -> i64
extern fn rt_string_to_byte_array(s: text) -> [u8]
extern fn rt_string_from_byte_array(arr: [u8]) -> text
extern fn rt_text_validate_utf8(s: text) -> bool
extern fn rt_random_randint(min: i64, max: i64) -> i64
extern fn rt_random_uniform(min: f64, max: f64) -> f64
extern fn rt_print_err(msg: text)
extern fn rt_shell_exec(cmd: text) -> text
extern fn rt_process_hwm_kib() -> i64
extern fn rt_heap_array_capacity_bytes() -> i64
extern fn rt_mem_attr_enabled() -> i64
extern fn rt_transient_array_scope_state_v1() -> i64
extern fn rt_process_last_child_peak_rss_kib() -> i64
extern fn rt_pty_resize(handle: i64, rows: i32, cols: i32) -> bool
extern fn rt_pty_read(handle: i64, timeout_ms: i64) -> text
extern fn rt_file_atomic_write_bytes_array(path: text, data: [u8]) -> bool

fn main():
    val p = "__P__"
    val m = rt_file_modified(p)
    val m2 = rt_file_modified_time(p)
    print "modified_pos={m > 0} same={m == m2}"
    print "modified_missing={rt_file_modified("/nonexistent/zzz")}"
    print "mode={rt_file_mode(p)} mode_missing={rt_file_mode("/nonexistent/zzz")}"
    val bytes = rt_string_to_byte_array("héllo")
    print "bytes_len={bytes.len()} b0={bytes[0]} b1={bytes[1]}"
    print "roundtrip=[{rt_string_from_byte_array(bytes)}]"
    val ok = rt_text_validate_utf8("héllo")
    if ok:
        print "utf8=true"
    else:
        print "utf8=false"
    print "randint={rt_random_randint(7, 7)}"
    val r = rt_random_randint(10, 20)
    print "randint_range={r >= 10 and r <= 20}"
    val u = rt_random_uniform(2.5, 2.5)
    print "uniform={u}"
    val u2 = rt_random_uniform(1.0, 3.0)
    print "uniform_range={u2 >= 1.0 and u2 <= 3.0}"
    rt_print_err("to-stderr\n")
    print "shell=[{rt_shell_exec("echo hi-from-shell")}]"
    print "hwm_pos={rt_process_hwm_kib() > 0}"
    print "heapcap_nonneg={rt_heap_array_capacity_bytes() >= 0} attr={rt_mem_attr_enabled()}"
    print "scope_state={rt_transient_array_scope_state_v1()}"
    print "child_rss_nonneg={rt_process_last_child_peak_rss_kib() >= 0}"
    val resized = rt_pty_resize(-1, 24, 80)
    var resized_text = "false"
    if resized:
        resized_text = "true"
    val wrote = rt_file_atomic_write_bytes_array("__P__.atomic", rt_string_to_byte_array("payload"))
    var wrote_text = "false"
    if wrote:
        wrote_text = "true"
    print "resize_bad={resized_text} atomic={wrote_text} atomic_mode_ok={rt_file_mode("__P__.atomic") >= 0}"
    print "pty_read_bad=[{rt_pty_read(-1, 0)}]"
"#;

/// Externs with a native provider and no interpreter handler: before
/// registration the bridge failed them at run time.
const NATIVE_ONLY: &str = r#"
extern fn rt_path_extension(path: text) -> text
extern fn rt_path_filename(path: text) -> text
extern fn rt_string_from_byte_array(arr: [u8]) -> text
extern fn rt_term_write(data: text) -> i64
extern fn rt_term_flush() -> i32
extern fn rt_stdin_read_all() -> [u8]
extern fn rt_stdin_read(size: i64) -> [u8]
extern fn rt_io_file_set_permissions(fd: i64, readonly: bool) -> bool
extern fn rt_io_file_meta_modified(fd: i64) -> i64

fn main():
    print "ext=[{rt_path_extension("/a/b/c.tar.gz")}] name=[{rt_path_filename("/a/b/c.tar.gz")}] noext=[{rt_path_extension("/a/b/c")}]"
    val w = rt_term_write("term-out\n")
    val f = rt_term_flush()
    print "term_write={w} flush={f}"
    val head = rt_stdin_read(3)
    print "stdin_head_len={head.len()} h0={head[0]}"
    val rest = rt_stdin_read_all()
    print "stdin_rest_len={rest.len()} text=[{rt_string_from_byte_array(rest)}]"
    val perm = rt_io_file_set_permissions(-1, true)
    var perm_text = "false"
    if perm:
        perm_text = "true"
    print "perm_bad={perm_text} meta_bad={rt_io_file_meta_modified(-1)}"
"#;

const NATIVE_ONLY_EXPECTED: &str = "ext=[gz] name=[c.tar.gz] noext=[]\nterm-out\nterm_write=9 flush=0\n\
stdin_head_len=3 h0=97\nstdin_rest_len=5 text=[defgh]\nperm_bad=false meta_bad=0\n";

const UNKNOWN_EXTERN: &str = r#"
extern fn rt_caret_jit_extern_gate_never_registered(x: i64) -> i64

fn main():
    print "before"
    val v = rt_caret_jit_extern_gate_never_registered(1)
    print "after={v}"
"#;

#[test]
fn registered_externs_link_natively_without_interpreter_splice() {
    for (tag, source) in [("backed", INTERP_BACKED), ("native", NATIVE_ONLY)] {
        let out = run(&write_source(tag, source), false, b"abcdefgh");
        let stderr = text(&out.stderr);
        assert!(
            !stderr.contains("hybrid-interp-splice"),
            "{tag}: registered externs were spliced through the interpreter:\n{stderr}"
        );
        assert!(out.status.success(), "{tag}: JIT run failed:\n{stderr}");
    }
}

#[test]
fn jit_and_interpreter_agree_on_registered_externs() {
    let path = write_source("parity", INTERP_BACKED);
    let jit = run(&path, false, b"");
    let interp = run(&path, true, b"");
    assert!(jit.status.success(), "JIT run failed:\n{}", text(&jit.stderr));
    assert!(interp.status.success(), "interpreter run failed:\n{}", text(&interp.stderr));
    assert_eq!(text(&jit.stdout), text(&interp.stdout));
    let stdout = text(&jit.stdout);
    for line in [
        "uniform=2.5",
        "randint=7",
        "roundtrip=[héllo]",
        "shell=[hi-from-shell",
        "mode_missing=-1",
        "resize_bad=false atomic=true atomic_mode_ok=true",
    ] {
        assert!(stdout.contains(line), "missing `{line}` in:\n{stdout}");
    }
    assert!(text(&jit.stderr).contains("to-stderr"));
}

#[test]
fn native_only_externs_return_the_runtime_values() {
    let out = run(&write_source("values", NATIVE_ONLY), false, b"abcdefgh");
    assert!(out.status.success(), "JIT run failed:\n{}", text(&out.stderr));
    assert_eq!(text(&out.stdout), NATIVE_ONLY_EXPECTED);
}

#[test]
fn unknown_extern_still_fails_closed() {
    let out = run(&write_source("unknown", UNKNOWN_EXTERN), false, b"");
    let stderr = text(&out.stderr);
    let stdout = text(&out.stdout);
    assert!(!out.status.success(), "an unbacked extern must not succeed:\n{stdout}\n{stderr}");
    assert!(stderr.contains("hybrid-interp-splice"), "{stderr}");
    assert!(stderr.contains("rt_caret_jit_extern_gate_never_registered"), "{stderr}");
    assert!(stderr.contains("backed by no implementation"), "{stderr}");
    assert!(!stdout.contains("after="), "{stdout}");
}

/// Wave 2: scalar-ABI C exports that also have an interpreter handler.
const WAVE2_INTERP_BACKED: &str = r#"
extern fn rt_time_now_seconds() -> i64
extern fn rt_time_now_seconds_f64() -> f64
extern fn rt_mem_guard_stats() -> i64
extern fn rt_mem_harden_check_native() -> i64
extern fn spl_thread_current_id() -> i64
extern fn rt_process_owned_v3_release_value(handle: i64) -> bool
extern fn rt_file_sync(path: text) -> bool
extern fn rt_file_create_excl(path: text, content: text) -> bool

fn flag(b: bool) -> text:
    if b:
        return "true"
    "false"

fn main():
    val s = rt_time_now_seconds()
    val f = rt_time_now_seconds_f64()
    print "seconds_sane={s > 1700000000} f64_sane={f > 1700000000.0} close={f - 5.0 < s + 5}"
    print "guard={rt_mem_guard_stats()} harden={rt_mem_harden_check_native()}"
    print "thread_pos={spl_thread_current_id() != 0}"
    print "release_bad={flag(rt_process_owned_v3_release_value(-1))}"
    print "sync_ok={flag(rt_file_sync("__P__"))} sync_missing={flag(rt_file_sync("__P__.missing"))}"
    print "excl_new={flag(rt_file_create_excl("__P__.excl__ENGINE__", "x"))} excl_again={flag(rt_file_create_excl("__P__.excl__ENGINE__", "x"))}"
"#;

/// Wave 2: scalar-ABI C exports with no interpreter handler, or whose handler
/// refuses ("process observation V4 is unavailable in interpreter mode").
const WAVE2_NATIVE_ONLY: &str = r#"
extern fn rt_alloc_probe_count_v1() -> i64
extern fn rt_alloc_probe_coverage_v1() -> i64
extern fn rt_alloc_probe_reset_v1()
extern fn rt_linux_group_cancel_v1(token: i64) -> i64
extern fn rt_linux_group_parent_release_v1(token: i64) -> i64
extern fn rt_process_observation_v4_reserved_state_value(token: i64) -> i64
extern fn rt_process_observation_v4_reserved_confirm_release_value(token: i64) -> i64
extern fn rt_process_observation_v4_reserved_matches_value(token: i64, rh: i64, rl: i64, th: i64, tl: i64) -> i64
extern fn rt_process_observation_v4_close_cwd_value(handle: i64) -> i32

fn main():
    rt_alloc_probe_reset_v1()
    print "probe_nonneg={rt_alloc_probe_count_v1() >= 0} coverage_nonneg={rt_alloc_probe_coverage_v1() >= 0}"
    print "cancel_bad_nonzero={rt_linux_group_cancel_v1(-1) != 0} release_bad_nonzero={rt_linux_group_parent_release_v1(-1) != 0}"
    print "state_bad={rt_process_observation_v4_reserved_state_value(-1)} confirm_bad={rt_process_observation_v4_reserved_confirm_release_value(-1)}"
    print "matches_bad={rt_process_observation_v4_reserved_matches_value(-1, 0, 0, 0, 0)} close_cwd_bad={rt_process_observation_v4_close_cwd_value(-1)}"
"#;

#[cfg(target_os = "linux")]
#[test]
fn wave2_scalar_c_externs_link_natively_and_match_the_interpreter() {
    let jit_path = write_source("w2jit", &WAVE2_INTERP_BACKED.replace("__ENGINE__", "jit"));
    let interp_path = write_source("w2int", &WAVE2_INTERP_BACKED.replace("__ENGINE__", "int"));
    let jit = run(&jit_path, false, b"");
    let interp = run(&interp_path, true, b"");
    let stderr = text(&jit.stderr);
    assert!(!stderr.contains("hybrid-interp-splice"), "spliced:\n{stderr}");
    assert!(jit.status.success(), "JIT run failed:\n{stderr}");
    assert!(interp.status.success(), "interpreter run failed:\n{}", text(&interp.stderr));
    assert_eq!(text(&jit.stdout), text(&interp.stdout));
    let stdout = text(&jit.stdout);
    for line in [
        "seconds_sane=true f64_sane=true close=true",
        "sync_ok=true sync_missing=false",
        "excl_new=true excl_again=false",
        "release_bad=false",
    ] {
        assert!(stdout.contains(line), "missing `{line}` in:\n{stdout}");
    }
}

#[cfg(target_os = "linux")]
#[test]
fn wave2_native_only_c_externs_link_natively() {
    let out = run(&write_source("w2native", WAVE2_NATIVE_ONLY), false, b"");
    let stderr = text(&out.stderr);
    assert!(!stderr.contains("hybrid-interp-splice"), "spliced:\n{stderr}");
    assert!(out.status.success(), "JIT run failed:\n{stderr}");
    let stdout = text(&out.stdout);
    for line in [
        "coverage_nonneg=true",
        "cancel_bad_nonzero=true release_bad_nonzero=true",
        "state_bad=-116 confirm_bad=-116",
        "matches_bad=-116 close_cwd_bad=0",
    ] {
        assert!(stdout.contains(line), "missing `{line}` in:\n{stdout}");
    }
}
