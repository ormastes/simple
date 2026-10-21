//! Real native shell ABI, independently of the interpreter dispatch table.
use simple_runtime::value::sffi::env_process::{rt_shell_exec, rt_shell_exec_tuple, rt_shell_exit_code};
use simple_runtime::value::{rt_string_data, rt_string_len, rt_string_new, rt_tuple_get, RuntimeValue};

fn text(value: &str) -> RuntimeValue {
    rt_string_new(value.as_ptr(), value.len() as u64)
}

fn decode(value: RuntimeValue) -> String {
    let len = rt_string_len(value) as usize;
    let bytes = unsafe { std::slice::from_raw_parts(rt_string_data(value), len) };
    String::from_utf8(bytes.to_vec()).unwrap()
}

fn nonzero_scalar() -> &'static str {
    if cfg!(windows) { "echo scalar-out& echo scalar-error 1>&2& exit /b 7" }
    else { "printf scalar-out; printf scalar-error >&2; exit 7" }
}

fn nonzero_tuple() -> &'static str {
    if cfg!(windows) { "echo tuple-out& echo tuple-error 1>&2& exit /b 3" }
    else { "printf tuple-out; printf tuple-error >&2; exit 3" }
}

#[test]
fn scalar_status_streams_tuple_noninterference_and_quoting() {
    unsafe {
        assert_eq!(rt_shell_exit_code(), 0);
        assert_eq!(decode(rt_shell_exec(text(nonzero_scalar()))).trim(), "scalar-out");
        assert_eq!(rt_shell_exit_code(), 7);
        let tuple = rt_shell_exec_tuple(text(nonzero_tuple()));
        assert_eq!(decode(rt_tuple_get(tuple, 0)).trim(), "tuple-out");
        assert_eq!(decode(rt_tuple_get(tuple, 1)).trim(), "tuple-error");
        assert_eq!(rt_tuple_get(tuple, 2).as_int(), 3);
        assert_eq!(rt_shell_exit_code(), 7);
        let tuple = rt_shell_exec_tuple(text("echo \"two words\""));
        let expected = if cfg!(windows) { "\"two words\"" } else { "two words" };
        assert_eq!(decode(rt_tuple_get(tuple, 0)).trim(), expected);
        assert_eq!(decode(rt_tuple_get(tuple, 1)), "");
        assert_eq!(rt_tuple_get(tuple, 2).as_int(), 0);
        assert_eq!(rt_shell_exit_code(), 7);
        assert_eq!(decode(rt_shell_exec(text("echo scalar-ok"))).trim(), "scalar-ok");
        assert_eq!(rt_shell_exit_code(), 0);
    }
}

#[test]
fn shell_status_is_isolated_between_real_threads() {
    use std::sync::{Arc, Barrier};
    let barrier = Arc::new(Barrier::new(2));
    let threads: Vec<_> = [4, 9].into_iter().map(|code| {
        let barrier = barrier.clone();
        std::thread::spawn(move || unsafe {
            assert_eq!(rt_shell_exit_code(), 0);
            let command = if cfg!(windows) { format!("exit /b {code}") } else { format!("exit {code}") };
            rt_shell_exec(text(&command));
            barrier.wait();
            assert_eq!(rt_shell_exit_code(), code);
        })
    }).collect();
    for thread in threads { thread.join().unwrap(); }
}
