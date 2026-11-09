//! Compile actual production adapters together with clashing externs denied.
//! Only interpreter value/error transport is narrowed for this standalone
//! boundary test. Every OS function is the real linked Windows implementation.
#![deny(clashing_extern_declarations)]
extern crate self as simple_runtime;
mod error {
    #[derive(Debug)]
    pub struct CompileError(String);
    impl CompileError { pub fn semantic(message: String) -> Self { Self(message) } }
}
mod value {
    use crate::error::CompileError;
    #[derive(Debug, PartialEq)]
    pub enum Value { Int(i64), Bool(bool), Str(String), Nil }
    impl Value {
        pub fn as_int(&self) -> Result<i64, CompileError> {
            match self { Self::Int(value) => Ok(*value), _ => Err(CompileError::semantic("integer required".into())) }
        }
        pub fn text(value: impl Into<String>) -> Self { Self::Str(value.into()) }
        pub fn to_display_string(&self) -> String { format!("{self:?}") }
    }
    pub mod pty { include!(concat!(env!("OUT_DIR"), "/runtime_pty_owner.rs")); }
}
#[path="../../../../src/compiler_rust/compiler/src/interpreter_extern/host_capacity_platform.rs"]
mod host_capacity_platform;
#[path="../../../../src/compiler_rust/compiler/src/interpreter_extern/windows_abi.rs"]
mod windows_abi;
#[path="../../../../src/compiler_rust/compiler/src/interpreter_extern/pty.rs"]
mod pty;
use value::Value;
fn call(name: &str, args: &[i64]) -> i64 {
    windows_abi::dispatch(name, &args.iter().copied().map(Value::Int).collect::<Vec<_>>()).unwrap().as_int().unwrap()
}
fn main() {
    use windows_sys::Win32::System::SystemInformation::MEMORYSTATUSEX;
    use windows_sys::Win32::System::Threading::{STARTUPINFOW, PROCESS_INFORMATION};
    use windows_sys::Win32::System::ProcessStatus::{PROCESS_MEMORY_COUNTERS, PROCESS_MEMORY_COUNTERS_EX};
    assert_eq!(std::mem::size_of::<MEMORYSTATUSEX>(),64);
    assert_eq!(std::mem::size_of::<STARTUPINFOW>(),104);
    assert_eq!(std::mem::size_of::<PROCESS_INFORMATION>(),24);
    assert_eq!(std::mem::size_of::<PROCESS_MEMORY_COUNTERS>(),72);
    assert_eq!(std::mem::size_of::<PROCESS_MEMORY_COUNTERS_EX>(),80);
    assert_eq!(std::mem::offset_of!(PROCESS_MEMORY_COUNTERS_EX,WorkingSetSize),16);
    assert!(host_capacity_platform::memory_headroom()>0);
    assert!(host_capacity_platform::commit_headroom()>0);
    assert!(host_capacity_platform::disk_headroom(".")>0);
    let mut memory: MEMORYSTATUSEX=unsafe {std::mem::zeroed()};
    memory.dwLength=64;
    assert_ne!(call("GlobalMemoryStatusEx", &[&mut memory as *mut _ as i64]),0);
    assert!(memory.ullTotalPhys>0 && memory.ullAvailPhys>0);
    let mut startup: STARTUPINFOW=unsafe {std::mem::zeroed()}; startup.cb=104;
    let mut info: PROCESS_INFORMATION=unsafe {std::mem::zeroed()};
    let mut command:Vec<u16>="cmd.exe /C exit 7\0".encode_utf16().collect();
    assert_ne!(call("CreateProcessW", &[0,command.as_mut_ptr() as i64,0,0,0,0,0,0,&mut startup as *mut _ as i64,&mut info as *mut _ as i64]),0);
    assert_eq!(call("WaitForSingleObject", &[info.hProcess as i64,5000]),0);
    let mut code=0u32;
    assert_ne!(call("GetExitCodeProcess", &[info.hProcess as i64,&mut code as *mut _ as i64]),0);
    assert_eq!(code,7);
    assert_ne!(call("CloseHandle", &[info.hThread as i64]),0);
    assert_ne!(call("CloseHandle", &[info.hProcess as i64]),0);
    let mut bad:Vec<u16>="Z:\\missing-abi-fixture\\none.exe\0".encode_utf16().collect();
    assert_eq!(call("CreateProcessW", &[bad.as_mut_ptr() as i64,0,0,0,0,0,0,0,&mut startup as *mut _ as i64,&mut info as *mut _ as i64]),0);
    let pty_source=include_str!("../../../../src/compiler_rust/compiler/src/interpreter_extern/pty.rs");
    assert!(!pty_source.contains("fn CreateProcessW("));
    assert!(pty_source.contains("simple_runtime::value::pty::host_pty_spawn(handle, shell)"));
    assert_eq!(pty::rt_pty_spawn(&[Value::Int(-1),Value::text("cmd.exe")]).unwrap(),Value::Int(-1));
    let handle=pty::rt_pty_open(&[Value::Int(24),Value::Int(80)]).unwrap().as_int().unwrap();
    assert!(handle>0);
    assert!(pty::rt_pty_spawn(&[Value::Int(handle),Value::text("cmd.exe")]).unwrap().as_int().unwrap()>0);
    assert_eq!(pty::rt_pty_write(&[Value::Int(handle),Value::text("echo ABI_PTY_OK\r\nexit\r\n")]).unwrap(),Value::Bool(true));
    let deadline=std::time::Instant::now()+std::time::Duration::from_secs(5);
    let mut output=String::new();
    while std::time::Instant::now()<deadline && !output.contains("ABI_PTY_OK") {
        if let Value::Str(text)=pty::rt_pty_read(&[Value::Int(handle),Value::Int(100)]).unwrap() {output.push_str(&text);}
    }
    assert_eq!(pty::rt_pty_close(&[Value::Int(handle)]).unwrap(),Value::Bool(true));
    assert!(output.contains("ABI_PTY_OK"), "ConPTY output: {output:?}");
    println!("PASS: real Windows memory/process ABI, layouts, failed create, and live PTY transport");
}
