//! Link the actual Rust host module with the actual C runtime translation unit.
//! This checks delegation and symbol composition, not an independent waitid port.
#[path = "../../compiler_rust/runtime/src/process_tree_observation_v1.rs"]
mod host_binding;

use std::io::Write;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

unsafe extern "C" {
    fn rt_process_owned_child_state(pid: i64) -> i64;
}

fn both(pid: i64, expected: i64) {
    let c = unsafe { rt_process_owned_child_state(pid) };
    let rust = host_binding::rt_process_owned_child_state(pid);
    assert_eq!(c, expected, "C owned-child observation");
    assert_eq!(rust, c, "Rust host alias preserves exact result");
}

fn main() {
    assert!(cfg!(target_os = "linux"), "this errno fixture is Linux-specific");
    both(1, -22);
    both(i64::from(std::process::id()), -10);
    let mut child = Command::new("/bin/sh")
        .args(["-c", "read token; exit 7"])
        .stdin(Stdio::piped())
        .spawn().expect("real child spawn");
    let pid = i64::from(child.id());
    both(pid, 1);
    child.stdin.take().expect("owned stdin").write_all(b"go\n").expect("release child");
    let deadline = Instant::now() + Duration::from_secs(2);
    while host_binding::rt_process_owned_child_state(pid) == 1 {
        assert!(Instant::now() < deadline, "child did not exit within bound");
        std::thread::sleep(Duration::from_millis(1));
    }
    both(pid, 0);
    both(pid, 0);
    assert_eq!(child.wait().expect("single actual reap").code(), Some(7));
    both(pid, -10);
    println!("Rust/C host delegation: 6 state observations and preserved exit7 PASS");
}
