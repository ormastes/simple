//! Interpreter bridges for bootstrap runtime services used by compiler sources.
//! The file and archive operations delegate to the existing native providers so
//! the seed observes the same exclusive-create and descriptor-pinning rules.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::RuntimeValue;

unsafe extern "C" {
    #[link_name = "rt_pinned_archive_open_beneath_v1"]
    fn c_pinned_archive_open_beneath(root: i64, path: i64) -> i64;
    #[link_name = "rt_pinned_archive_device_v1"]
    fn c_pinned_archive_device(handle: i64) -> i64;
    #[link_name = "rt_pinned_archive_inode_v1"]
    fn c_pinned_archive_inode(handle: i64) -> i64;
    #[link_name = "rt_pinned_archive_size_v1"]
    fn c_pinned_archive_size(handle: i64) -> i64;
    #[link_name = "rt_pinned_archive_close_v1"]
    fn c_pinned_archive_close(handle: i64) -> i8;
    #[link_name = "rt_simple_abi_version"]
    fn c_simple_abi_version() -> i64;
    #[link_name = "rt_simple_abi_version_deferred"]
    fn c_simple_abi_version_deferred() -> i64;
}

fn text_arg<'a>(args: &'a [Value], index: usize, name: &str) -> Result<&'a str, CompileError> {
    match args.get(index) {
        Some(Value::Str(value)) => Ok(value.as_str()),
        _ => Err(CompileError::runtime(format!("{name}: argument {index} must be text"))),
    }
}

fn int_arg(args: &[Value], index: usize, name: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!(
            "{name}: argument {index} must be an integer"
        ))),
    }
}

struct RuntimeText(RuntimeValue);

impl RuntimeText {
    fn new(text: &str) -> Self {
        Self(simple_runtime::value::rt_string_new(text.as_ptr(), text.len() as u64))
    }

    fn raw(&self) -> i64 {
        self.0.to_raw() as i64
    }
}

impl Drop for RuntimeText {
    fn drop(&mut self) {
        let _ = simple_runtime::value::rt_string_free(self.0);
    }
}

pub fn rt_file_copy_create_excl_no_follow(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_file_copy_create_excl_no_follow";
    let source = text_arg(args, 0, NAME)?;
    let destination = text_arg(args, 1, NAME)?;
    let ok = unsafe {
        simple_runtime::value::sffi::file_io::file_ops::rt_file_copy_create_excl_no_follow(
            source.as_ptr(),
            source.len() as u64,
            destination.as_ptr(),
            destination.len() as u64,
        )
    };
    Ok(Value::Bool(ok))
}

pub fn rt_file_link_create_excl_no_follow(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_file_link_create_excl_no_follow";
    let source = text_arg(args, 0, NAME)?;
    let destination = text_arg(args, 1, NAME)?;
    let ok = unsafe {
        simple_runtime::value::sffi::file_io::file_ops::rt_file_link_create_excl_no_follow(
            source.as_ptr(),
            source.len() as u64,
            destination.as_ptr(),
            destination.len() as u64,
        )
    };
    Ok(Value::Bool(ok))
}

pub fn rt_pinned_archive_open_beneath_v1(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_pinned_archive_open_beneath_v1";
    let root = RuntimeText::new(text_arg(args, 0, NAME)?);
    let path = RuntimeText::new(text_arg(args, 1, NAME)?);
    Ok(Value::Int(unsafe {
        c_pinned_archive_open_beneath(root.raw(), path.raw())
    }))
}

pub fn rt_pinned_archive_device_v1(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(unsafe {
        c_pinned_archive_device(int_arg(args, 0, "rt_pinned_archive_device_v1")?)
    }))
}

pub fn rt_pinned_archive_inode_v1(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(unsafe {
        c_pinned_archive_inode(int_arg(args, 0, "rt_pinned_archive_inode_v1")?)
    }))
}

pub fn rt_pinned_archive_size_v1(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(unsafe {
        c_pinned_archive_size(int_arg(args, 0, "rt_pinned_archive_size_v1")?)
    }))
}

pub fn rt_pinned_archive_close_v1(args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(unsafe {
        c_pinned_archive_close(int_arg(args, 0, "rt_pinned_archive_close_v1")?) != 0
    }))
}

pub fn rt_simple_abi_version(args: &[Value]) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::runtime("rt_simple_abi_version takes no arguments"));
    }
    Ok(Value::Int(unsafe { c_simple_abi_version() }))
}

pub fn rt_simple_abi_version_deferred(args: &[Value]) -> Result<Value, CompileError> {
    if !args.is_empty() {
        return Err(CompileError::runtime(
            "rt_simple_abi_version_deferred takes no arguments",
        ));
    }
    Ok(Value::Int(unsafe { c_simple_abi_version_deferred() }))
}

/// Process birth identity must use the same OS unit as the native runtime:
/// Linux /proc start ticks, or Windows FILETIME ticks. Zero means unavailable.
pub fn rt_process_start_identity(args: &[Value]) -> Result<Value, CompileError> {
    let pid = int_arg(args, 0, "rt_process_start_identity")?;
    if pid <= 0 {
        return Ok(Value::Int(0));
    }
    #[cfg(target_os = "linux")]
    {
        let identity = std::fs::read_to_string(format!("/proc/{pid}/stat"))
            .ok()
            .and_then(|stat| {
                let tail = stat.get(stat.rfind(')')? + 2..)?;
                tail.split_whitespace().nth(19)?.parse::<i64>().ok()
            })
            .filter(|identity| *identity > 0)
            .unwrap_or(0);
        return Ok(Value::Int(identity));
    }
    #[cfg(windows)]
    {
        use windows_sys::Win32::Foundation::{CloseHandle, FILETIME};
        use windows_sys::Win32::System::Threading::{GetProcessTimes, OpenProcess, PROCESS_QUERY_LIMITED_INFORMATION};
        if pid > u32::MAX as i64 {
            return Ok(Value::Int(0));
        }
        let process = unsafe { OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, 0, pid as u32) };
        if process.is_null() {
            return Ok(Value::Int(0));
        }
        let mut created: FILETIME = unsafe { std::mem::zeroed() };
        let mut exited: FILETIME = unsafe { std::mem::zeroed() };
        let mut kernel: FILETIME = unsafe { std::mem::zeroed() };
        let mut user: FILETIME = unsafe { std::mem::zeroed() };
        let ok = unsafe { GetProcessTimes(process, &mut created, &mut exited, &mut kernel, &mut user) } != 0;
        unsafe { CloseHandle(process) };
        if !ok {
            return Ok(Value::Int(0));
        }
        let identity = ((created.dwHighDateTime as u64) << 32) | created.dwLowDateTime as u64;
        return Ok(Value::Int(i64::try_from(identity).unwrap_or(0)));
    }
    #[cfg(not(any(target_os = "linux", windows)))]
    Ok(Value::Int(0))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text(value: &str) -> Value {
        Value::text(value.to_owned())
    }

    #[test]
    fn abi_version_comes_from_the_selected_runtime() {
        let Value::Int(version) = rt_simple_abi_version(&[]).unwrap() else {
            panic!("version type")
        };
        let Value::Int(deferred) = rt_simple_abi_version_deferred(&[]).unwrap() else {
            panic!("deferred type")
        };
        assert!((version == 0 && deferred == 1) || (version > 0 && deferred == 0));
    }

    #[cfg(any(target_os = "linux", windows))]
    #[test]
    fn process_start_identity_is_stable_for_the_current_process() {
        let pid = Value::Int(std::process::id() as i64);
        let first = rt_process_start_identity(&[pid.clone()]).unwrap();
        assert!(matches!(first, Value::Int(value) if value > 0));
        assert_eq!(first, rt_process_start_identity(&[pid]).unwrap());
    }

    #[cfg(unix)]
    #[test]
    fn secure_file_and_pinned_archive_handlers_use_native_contracts() {
        let dir = tempfile::tempdir().unwrap();
        let source = dir.path().join("source");
        let copy = dir.path().join("copy");
        let link = dir.path().join("link");
        std::fs::write(&source, b"archive").unwrap();
        let source = text(&source.to_string_lossy());
        let copy_arg = text(&copy.to_string_lossy());
        let link_arg = text(&link.to_string_lossy());
        assert_eq!(
            rt_file_copy_create_excl_no_follow(&[source.clone(), copy_arg.clone()]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            rt_file_copy_create_excl_no_follow(&[source.clone(), copy_arg]).unwrap(),
            Value::Bool(false)
        );
        assert_eq!(
            rt_file_link_create_excl_no_follow(&[source, link_arg.clone()]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            rt_file_link_create_excl_no_follow(&[text(&copy.to_string_lossy()), link_arg]).unwrap(),
            Value::Bool(false)
        );

        let root = text(&dir.path().to_string_lossy());
        let Value::Int(handle) = rt_pinned_archive_open_beneath_v1(&[root, text("copy")]).unwrap() else {
            panic!("handle type")
        };
        assert!(handle > 0);
        assert_eq!(rt_pinned_archive_size_v1(&[Value::Int(handle)]).unwrap(), Value::Int(7));
        assert!(matches!(rt_pinned_archive_device_v1(&[Value::Int(handle)]).unwrap(), Value::Int(value) if value >= 0));
        assert!(matches!(rt_pinned_archive_inode_v1(&[Value::Int(handle)]).unwrap(), Value::Int(value) if value >= 0));
        assert_eq!(
            rt_pinned_archive_close_v1(&[Value::Int(handle)]).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            rt_pinned_archive_size_v1(&[Value::Int(handle)]).unwrap(),
            Value::Int(-1)
        );
    }
}
