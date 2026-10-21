#![cfg(windows)]
use simple_runtime::value::{rt_array_get, rt_array_len, rt_array_new, rt_array_push, rt_string_new, rt_tuple_get};
use simple_runtime::value::sffi::env_process::rt_process_run_bounded_bytes;
use simple_runtime::value::RuntimeValue;
use std::time::{Duration, Instant};

unsafe fn capture(exe: &str, args: &[&str], timeout: i64, cap: i64) -> (Vec<u8>, Vec<u8>, i64) {
    let input = rt_array_new(args.len() as u64);
    for arg in args { assert!(rt_array_push(input, rt_string_new(arg.as_ptr(), arg.len() as u64))); }
    let result = rt_process_run_bounded_bytes(exe.as_ptr(), exe.len() as u64, input, timeout, cap);
    let bytes = |value: RuntimeValue| (0..rt_array_len(value)).map(|i| rt_array_get(value, i).as_int() as u8).collect();
    (bytes(rt_tuple_get(result, 0)), bytes(rt_tuple_get(result, 1)), rt_tuple_get(result, 2).as_int())
}

unsafe fn assert_dead(pid: u32) {
    use windows::Win32::Foundation::CloseHandle;
    use windows::Win32::System::Threading::{OpenProcess, WaitForSingleObject, PROCESS_SYNCHRONIZE};
    if let Ok(process) = OpenProcess(PROCESS_SYNCHRONIZE, false, pid) {
        let status = WaitForSingleObject(process, 2000);
        let _ = CloseHandle(process);
        assert_eq!(status.0, 0, "grandchild still alive");
    }
}

unsafe fn resources() -> (u32, u32) {
    use windows::Win32::Foundation::CloseHandle;
    use windows::Win32::System::Diagnostics::ToolHelp::{CreateToolhelp32Snapshot, Thread32First, Thread32Next, THREADENTRY32, TH32CS_SNAPTHREAD};
    use windows::Win32::System::Threading::{GetCurrentProcess, GetCurrentProcessId, GetProcessHandleCount};
    let mut handles = 0;
    GetProcessHandleCount(GetCurrentProcess(), &mut handles).unwrap();
    let snapshot = CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0).unwrap();
    let mut entry = THREADENTRY32 { dwSize: std::mem::size_of::<THREADENTRY32>() as u32, ..Default::default() };
    let mut found = Thread32First(snapshot, &mut entry).is_ok();
    let mut threads = 0;
    while found {
        if entry.th32OwnerProcessID == GetCurrentProcessId() { threads += 1; }
        found = Thread32Next(snapshot, &mut entry).is_ok();
    }
    CloseHandle(snapshot).unwrap();
    (handles, threads)
}

#[test]
fn raw_capture_unicode_malformed_caps_status_and_owned_descendants() {
    let exe = std::env::var("SIMPLE_PROCESS_BYTES_CHILD").expect("actual native child fixture required");
    assert!(exe.contains('한'), "fixture executable path must itself contain Unicode");
    unsafe {
        let value = "한글 😀 quoted \"argument\" \\";
        let (out, err, code) = capture(&exe, &["echo", value], 3000, 4096);
        assert_eq!((out.as_slice(), err.as_slice(), code), (value.as_bytes(), value.as_bytes(), 7));
        std::thread::sleep(Duration::from_millis(50));
        let baseline = resources();
        let malformed = vec![b'A', 0, 255, 0xe2, 0x82];
        let (out, err, code) = capture(&exe, &["malformed"], 3000, 4096);
        assert_eq!((out, err, code), (malformed.clone(), malformed, 9));
        let (out, err, code) = capture(&exe, &["cap"], 3000, 33);
        assert_eq!(out, (0..33).map(|i| b'A' + i % 26).collect::<Vec<_>>());
        assert_eq!(err, (0..33).map(|i| b'a' + i % 26).collect::<Vec<_>>());
        assert_eq!(code, 0);
        let (out, err, code) = capture(&exe, &["cap"], 3000, 0);
        assert_eq!((out, err, code), (vec![], vec![], 0));
        let (out, err, code) = capture(&exe, &["sleep"], 50, 0);
        assert_eq!((out, err, code), (vec![], vec![], -1));
        for mode in ["tree", "root-exit"] {
            let started = Instant::now();
            let (out, err, code) = capture(&exe, &[mode], 1500, 128);
            assert!(started.elapsed() < Duration::from_secs(4), "capture exceeded its finite deadline");
            assert_eq!(code, if mode == "tree" { -1 } else { 0 });
            assert!(err.is_empty());
            let pid: u32 = std::str::from_utf8(&out).unwrap().parse().expect("grandchild pid was not retained");
            assert_dead(pid);
        }
        std::thread::sleep(Duration::from_millis(50));
        let after = resources();
        assert!(after.0 <= baseline.0, "capture leaked process/job/pipe handles: {baseline:?} -> {after:?}");
        assert!(after.1 <= baseline.1, "capture leaked reader threads: {baseline:?} -> {after:?}");
    }
}
