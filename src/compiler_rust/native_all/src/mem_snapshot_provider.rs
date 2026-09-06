//! Bootstrap-native durable compiler evidence provider.

use std::fmt::{self, Write as _};

const PATH_CAP: usize = 4096;
const TOKEN_CAP: usize = 4096;
const LINE_CAP: usize = 8192;

struct StackText<const N: usize> {
    bytes: [u8; N],
    len: usize,
}

impl<const N: usize> StackText<N> {
    const fn new() -> Self {
        Self { bytes: [0; N], len: 0 }
    }

    fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl<const N: usize> fmt::Write for StackText<N> {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        let end = self.len.checked_add(value.len()).ok_or(fmt::Error)?;
        if end > N {
            return Err(fmt::Error);
        }
        self.bytes[self.len..end].copy_from_slice(value.as_bytes());
        self.len = end;
        Ok(())
    }
}

fn encode_token<const N: usize>(input: &[u8]) -> Option<StackText<N>> {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut output = StackText::new();
    for &byte in input {
        if matches!(byte, b'%' | b' ' | b'=' | b'\n' | b'\r') {
            if output.len + 3 > N {
                return None;
            }
            output.bytes[output.len] = b'%';
            output.bytes[output.len + 1] = HEX[(byte >> 4) as usize];
            output.bytes[output.len + 2] = HEX[(byte & 15) as usize];
            output.len += 3;
        } else {
            if output.len == N {
                return None;
            }
            output.bytes[output.len] = byte;
            output.len += 1;
        }
    }
    Some(output)
}

unsafe fn input_bytes<'a>(ptr: *const u8, len: i64) -> Option<&'a [u8]> {
    if len < 0 || (len > 0 && ptr.is_null()) {
        return None;
    }
    Some(if len == 0 {
        &[]
    } else {
        // SAFETY: The Simple native ABI guarantees that text pointers remain valid
        // for the duration of the extern call.
        unsafe { std::slice::from_raw_parts(ptr, usize::try_from(len).ok()?) }
    })
}

#[cfg(unix)]
fn monotonic_ms() -> Option<i64> {
    let mut value = libc::timespec { tv_sec: 0, tv_nsec: 0 };
    // SAFETY: `value` is a valid writable timespec.
    if unsafe { libc::clock_gettime(libc::CLOCK_MONOTONIC, &mut value) } != 0 {
        return None;
    }
    value.tv_sec.checked_mul(1000)?.checked_add(value.tv_nsec / 1_000_000)
}

#[cfg(unix)]
fn run_id_token() -> Option<StackText<256>> {
    static KEY: &[u8] = b"SIMPLE_EVIDENCE_RUN_ID\0";
    // SAFETY: KEY is statically NUL terminated; getenv's result is inspected only
    // during this call and never retained.
    let ptr = unsafe { libc::getenv(KEY.as_ptr().cast()) };
    if ptr.is_null() {
        return encode_token(b"-");
    }
    let mut len = 0usize;
    // Bound both the environment read and its encoded representation.
    while len < 255 && unsafe { *ptr.add(len) } != 0 {
        len += 1;
    }
    if len == 255 && unsafe { *ptr.add(len) } != 0 {
        return None;
    }
    // SAFETY: getenv returned a NUL-terminated string and the bounded scan found it.
    encode_token(unsafe { std::slice::from_raw_parts(ptr.cast(), len) })
}

#[cfg(unix)]
fn append_flush(fd: i64, record: &[u8]) -> bool {
    if fd < 0 || fd > i32::MAX as i64 || record.last() != Some(&b'\n') {
        return false;
    }
    let mut offset = 0usize;
    while offset < record.len() {
        // SAFETY: record[offset..] is readable and fd was supplied by the ABI.
        let wrote = unsafe { libc::write(fd as i32, record[offset..].as_ptr().cast(), record.len() - offset) };
        if wrote <= 0 {
            return false;
        }
        offset += wrote as usize;
    }
    // SAFETY: fd is range checked above.
    unsafe { libc::fsync(fd as i32) == 0 }
}

#[cfg(unix)]
unsafe fn secure_open(path_ptr: *const u8, path_len: i64) -> i64 {
    let path = match unsafe { input_bytes(path_ptr, path_len) } {
        Some(value) if !value.is_empty() && value.len() < PATH_CAP && !value.contains(&0) => value,
        _ => return -1,
    };
    if path.last() == Some(&b'/') {
        return -1;
    }
    let mut copy = [0u8; PATH_CAP];
    copy[..path.len()].copy_from_slice(path);
    copy[path.len()] = 0;

    let root: &[u8] = if path[0] == b'/' { b"/\0" } else { b".\0" };
    // SAFETY: root is NUL terminated.
    let mut parent = unsafe {
        libc::open(
            root.as_ptr().cast(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC,
        )
    };
    if parent < 0 {
        return -1;
    }

    let mut cursor = usize::from(path[0] == b'/');
    let mut segments = [(0usize, 0usize); PATH_CAP / 2];
    let mut count = 0usize;
    while cursor < path.len() {
        while cursor < path.len() && path[cursor] == b'/' {
            cursor += 1;
        }
        if cursor == path.len() {
            break;
        }
        let start = cursor;
        while cursor < path.len() && path[cursor] != b'/' {
            cursor += 1;
        }
        if count == segments.len() {
            // SAFETY: parent is an owned open descriptor.
            unsafe { libc::close(parent) };
            return -1;
        }
        segments[count] = (start, cursor);
        count += 1;
    }
    if count == 0 {
        unsafe { libc::close(parent) };
        return -1;
    }

    for &(start, end) in &segments[..count - 1] {
        let part = &path[start..end];
        if part == b"." {
            continue;
        }
        if part == b".." {
            unsafe { libc::close(parent) };
            return -1;
        }
        copy[end] = 0;
        let next = unsafe {
            libc::openat(
                parent,
                copy[start..].as_ptr().cast(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            )
        };
        unsafe { libc::close(parent) };
        if next < 0 {
            return -1;
        }
        parent = next;
    }

    let (leaf_start, leaf_end) = segments[count - 1];
    let leaf = &path[leaf_start..leaf_end];
    if leaf == b"." || leaf == b".." {
        unsafe { libc::close(parent) };
        return -1;
    }
    copy[leaf_end] = 0;
    let fd = unsafe {
        libc::openat(
            parent,
            copy[leaf_start..].as_ptr().cast(),
            libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_APPEND | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0o600,
        )
    };
    unsafe { libc::close(parent) };
    if fd < 0 {
        return -1;
    }
    let mut stat: libc::stat = unsafe { std::mem::zeroed() };
    if unsafe { libc::fstat(fd, &mut stat) } != 0 || stat.st_mode & libc::S_IFMT != libc::S_IFREG {
        unsafe { libc::close(fd) };
        return -1;
    }
    fd as i64
}

#[no_mangle]
pub unsafe extern "C" fn rt_mem_snapshot_open(path: *const u8, path_len: i64) -> i64 {
    #[cfg(unix)]
    return unsafe { secure_open(path, path_len) };
    #[cfg(not(unix))]
    {
        let _ = (path, path_len);
        -1
    }
}

#[cfg(unix)]
fn process_status_kib(key: &[u8]) -> i64 {
    static STATUS: &[u8] = b"/proc/self/status\0";
    let fd = unsafe { libc::open(STATUS.as_ptr().cast(), libc::O_RDONLY | libc::O_CLOEXEC) };
    if fd < 0 {
        return -1;
    }
    let mut bytes = [0u8; 8192];
    let read = unsafe { libc::read(fd, bytes.as_mut_ptr().cast(), bytes.len()) };
    unsafe { libc::close(fd) };
    if read <= 0 {
        return -1;
    }
    for line in bytes[..read as usize].split(|byte| *byte == b'\n') {
        if let Some(rest) = line.strip_prefix(key) {
            let digits = rest
                .iter()
                .skip_while(|byte| byte.is_ascii_whitespace())
                .take_while(|byte| byte.is_ascii_digit());
            let mut value = 0i64;
            let mut found = false;
            for digit in digits {
                found = true;
                value = match value.checked_mul(10).and_then(|v| v.checked_add((digit - b'0') as i64)) {
                    Some(value) => value,
                    None => return -1,
                };
            }
            return if found { value } else { -1 };
        }
    }
    -1
}

#[allow(clippy::too_many_arguments)]
#[no_mangle]
pub unsafe extern "C" fn rt_mem_snapshot_record(
    fd: i64,
    seq: i64,
    event: *const u8,
    event_len: i64,
    phase: *const u8,
    phase_len: i64,
    source_index: i64,
    source_path: *const u8,
    source_path_len: i64,
    retained_modules: i64,
    validation_keys: i64,
    validation_values: i64,
    shared_traits: i64,
    hir_names: i64,
    hir_symbols: i64,
    hir_functions: i64,
    hir_constants: i64,
    hir_enums: i64,
    hir_structs: i64,
    hir_classes: i64,
) -> bool {
    #[cfg(not(unix))]
    {
        let _ = (
            fd,
            seq,
            event,
            event_len,
            phase,
            phase_len,
            source_index,
            source_path,
            source_path_len,
            retained_modules,
            validation_keys,
            validation_values,
            shared_traits,
            hir_names,
            hir_symbols,
            hir_functions,
            hir_constants,
            hir_enums,
            hir_structs,
            hir_classes,
        );
        return false;
    }
    #[cfg(unix)]
    {
        let event = match unsafe { input_bytes(event, event_len) }.and_then(encode_token::<64>) {
            Some(value) => value,
            None => return false,
        };
        let phase = match unsafe { input_bytes(phase, phase_len) }.and_then(encode_token::<128>) {
            Some(value) => value,
            None => return false,
        };
        let path = match unsafe { input_bytes(source_path, source_path_len) }.and_then(encode_token::<TOKEN_CAP>) {
            Some(value) => value,
            None => return false,
        };
        let run_id = match run_id_token() {
            Some(value) => value,
            None => return false,
        };
        let now = match monotonic_ms() {
            Some(value) => value,
            None => return false,
        };
        let path_kind = if source_path_len > 0 { "recorded" } else { "none" };
        let emitted_path = if source_path_len > 0 { path.as_bytes() } else { b"-" };
        let mut line = StackText::<LINE_CAP>::new();
        let ok = write!(&mut line,
            "schema=simple.compiler.mem_snapshot.v1 run_id={} seq={seq} pid={} monotonic_ms={now} event={} phase={} source_index={source_index} source_path_kind={path_kind} source_path={} retained_modules={retained_modules} validation_keys={validation_keys} validation_values={validation_values} shared_traits={shared_traits} hir_names={hir_names} hir_symbols={hir_symbols} hir_functions={hir_functions} hir_constants={hir_constants} hir_enums={hir_enums} hir_structs={hir_structs} hir_classes={hir_classes} heap_live_bytes={} heap_peak_bytes={} rss_kib={} hwm_kib={}\n",
            StringView(run_id.as_bytes()), unsafe { libc::getpid() }, StringView(event.as_bytes()),
            StringView(phase.as_bytes()), StringView(emitted_path),
            simple_runtime::value::heap::rt_heap_live_bytes(),
            simple_runtime::value::heap::rt_heap_peak_bytes(),
            process_status_kib(b"VmRSS:"), process_status_kib(b"VmHWM:")).is_ok();
        ok && append_flush(fd, line.as_bytes())
    }
}

struct StringView<'a>(&'a [u8]);
impl fmt::Display for StringView<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(std::str::from_utf8(self.0).map_err(|_| fmt::Error)?)
    }
}

#[no_mangle]
pub unsafe extern "C" fn rt_phase_profile_record(fd: i64, seq: i64, message: *const u8, message_len: i64) -> bool {
    #[cfg(not(unix))]
    {
        let _ = (fd, seq, message, message_len);
        return false;
    }
    #[cfg(unix)]
    {
        let message = match unsafe { input_bytes(message, message_len) }.and_then(encode_token::<TOKEN_CAP>) {
            Some(value) => value,
            None => return false,
        };
        let run_id = match run_id_token() {
            Some(value) => value,
            None => return false,
        };
        let now = match monotonic_ms() {
            Some(value) => value,
            None => return false,
        };
        let mut line = StackText::<LINE_CAP>::new();
        let ok = write!(
            &mut line,
            "schema=simple.compiler.phase_profile.v1 run_id={} seq={seq} pid={} monotonic_ms={now} message={}\n",
            StringView(run_id.as_bytes()),
            unsafe { libc::getpid() },
            StringView(message.as_bytes())
        )
        .is_ok();
        ok && append_flush(fd, line.as_bytes())
    }
}

#[no_mangle]
pub extern "C" fn rt_mem_snapshot_close(fd: i64) -> bool {
    #[cfg(unix)]
    return fd >= 0 && fd <= i32::MAX as i64 && unsafe { libc::close(fd as i32) == 0 };
    #[cfg(not(unix))]
    {
        let _ = fd;
        false
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::ffi::OsStrExt;

    #[test]
    fn secure_open_is_exclusive_and_rejects_symlinked_parent() {
        let dir = tempfile::tempdir().unwrap();
        let target = dir.path().join("evidence.log");
        let bytes = target.as_os_str().as_bytes();
        let fd = unsafe { rt_mem_snapshot_open(bytes.as_ptr(), bytes.len() as i64) };
        assert!(fd >= 0);
        assert!(rt_mem_snapshot_close(fd));
        assert_eq!(unsafe { rt_mem_snapshot_open(bytes.as_ptr(), bytes.len() as i64) }, -1);

        let link = dir.path().join("link");
        std::os::unix::fs::symlink(dir.path(), &link).unwrap();
        let linked_target = link.join("other.log");
        let linked = linked_target.as_os_str().as_bytes();
        assert_eq!(
            unsafe { rt_mem_snapshot_open(linked.as_ptr(), linked.len() as i64) },
            -1
        );
    }

    #[test]
    fn token_encoding_is_bounded_and_schema_safe() {
        let token = encode_token::<32>(b"a b=c%\r\n").unwrap();
        assert_eq!(token.as_bytes(), b"a%20b%3Dc%25%0D%0A");
        assert!(encode_token::<2>(b" ").is_none());
    }
}
