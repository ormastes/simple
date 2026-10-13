//! Bootstrap-native durable compiler evidence provider.

use std::fmt::{self, Write as _};

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
    // Encoding cannot shrink its input. Refuse oversized messages before
    // constructing or reading a caller-provided slice.
    if len < 0 || len > TOKEN_CAP as i64 || (len > 0 && ptr.is_null()) {
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

#[cfg(windows)]
#[link(name = "kernel32")]
extern "system" {
    fn GetTickCount64() -> u64;
    fn GetCurrentProcessId() -> u32;
    fn GetEnvironmentVariableW(name: *const u16, buffer: *mut u16, size: u32) -> u32;
    fn GetLastError() -> u32;
    fn SetLastError(error: u32);
}

#[cfg(windows)]
fn monotonic_ms() -> Option<i64> {
    // SAFETY: no arguments or caller-owned pointers.
    i64::try_from(unsafe { GetTickCount64() }).ok()
}

#[cfg(windows)]
fn run_id_token() -> Option<StackText<256>> {
    const KEY: &[u16] = &[
        83, 73, 77, 80, 76, 69, 95, 69, 86, 73, 68, 69, 78, 67, 69, 95, 82, 85, 78, 95, 73, 68, 0,
    ]; // SIMPLE_EVIDENCE_RUN_ID
    let mut wide = [0u16; 256];
    // SAFETY: KEY is terminated and wide has the stated writable capacity.
    let len = unsafe {
        SetLastError(0);
        GetEnvironmentVariableW(KEY.as_ptr(), wide.as_mut_ptr(), wide.len() as u32)
    };
    if len == 0 {
        // Empty/unset run IDs use the established sentinel; other API errors
        // cannot silently become a successful evidence record.
        return match unsafe { GetLastError() } {
            0 | 203 => encode_token(b"-"), // ERROR_ENVVAR_NOT_FOUND
            _ => None,
        };
    }
    if len as usize >= wide.len() {
        return None;
    }
    let mut utf8 = StackText::<256>::new();
    for scalar in char::decode_utf16(wide[..len as usize].iter().copied()) {
        utf8.write_char(scalar.ok()?).ok()?;
    }
    encode_token(utf8.as_bytes())
}

#[cfg(windows)]
fn append_flush(fd: i64, record: &[u8]) -> bool {
    // The runtime owner validates the raw Win32 HANDLE, writes all bytes and
    // flushes. Never narrow it to a CRT fd or close the shared sink here.
    simple_runtime::mem_snapshot::windows_append_flush(fd, record)
}

#[cfg(windows)]
fn process_id() -> u32 {
    // SAFETY: no arguments or caller-owned pointers.
    unsafe { GetCurrentProcessId() }
}

#[cfg(unix)]
fn process_id() -> libc::pid_t {
    // SAFETY: getpid has no arguments.
    unsafe { libc::getpid() }
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

struct StringView<'a>(&'a [u8]);
impl fmt::Display for StringView<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(std::str::from_utf8(self.0).map_err(|_| fmt::Error)?)
    }
}

#[no_mangle]
pub unsafe extern "C" fn rt_phase_profile_record(fd: i64, seq: i64, message: *const u8, message_len: i64) -> bool {
    #[cfg(not(any(unix, windows)))]
    {
        let _ = (fd, seq, message, message_len);
        return false;
    }
    #[cfg(any(unix, windows))]
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
            process_id(),
            StringView(message.as_bytes())
        )
        .is_ok();
        ok && append_flush(fd, line.as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(windows)]
    static RUN_ID_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    #[cfg(windows)]
    struct RestoreRunId(Option<std::ffi::OsString>);

    #[cfg(windows)]
    impl Drop for RestoreRunId {
        fn drop(&mut self) {
            // Tests using the process-wide run ID hold RUN_ID_ENV_LOCK. The
            // bootstrap provider test invocation additionally uses one thread.
            unsafe {
                match &self.0 {
                    Some(value) => std::env::set_var("SIMPLE_EVIDENCE_RUN_ID", value),
                    None => std::env::remove_var("SIMPLE_EVIDENCE_RUN_ID"),
                }
            }
        }
    }

    #[test]
    fn token_encoding_is_bounded_and_schema_safe() {
        let token = encode_token::<32>(b"a b=c%\r\n").unwrap();
        assert_eq!(token.as_bytes(), b"a%20b%3Dc%25%0D%0A");
        assert!(encode_token::<2>(b" ").is_none());
    }

    #[cfg(windows)]
    #[test]
    fn windows_phase_records_use_owned_sink_and_real_process_identity() {
        use simple_runtime::mem_snapshot::{rt_mem_snapshot_close, rt_mem_snapshot_open};
        let _environment = RUN_ID_ENV_LOCK.lock().unwrap();
        let dir = std::env::temp_dir().join(format!(
            "simple-phase-provider-{}-{}",
            process_id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("phase.log");
        let text = path.to_str().unwrap();
        let fd = unsafe { rt_mem_snapshot_open(text.as_ptr(), text.len() as i64) };
        assert!(fd > 0);
        let message = b"hir done=2%\r\n";
        assert!(unsafe { rt_phase_profile_record(fd, 7, message.as_ptr(), message.len() as i64) });
        // Same handle remains live after the phase write; the phase provider
        // neither consumes nor closes the runtime owner's sink.
        assert!(unsafe { rt_phase_profile_record(fd, 8, b"next".as_ptr(), 4) });
        assert_eq!(rt_mem_snapshot_close(fd), 1);
        let content = std::fs::read_to_string(&path).unwrap();
        let lines: Vec<_> = content.lines().collect();
        assert_eq!(lines.len(), 2);
        assert!(lines[0].starts_with("schema=simple.compiler.phase_profile.v1 run_id="));
        assert!(lines[0].contains(&format!(" seq=7 pid={} monotonic_ms=", process_id())));
        assert!(lines[0].ends_with(" message=hir%20done%3D2%25%0D%0A"));
        assert_eq!(
            lines[0]
                .split(' ')
                .map(|field| field.split_once('=').unwrap().0)
                .collect::<Vec<_>>(),
            ["schema", "run_id", "seq", "pid", "monotonic_ms", "message"]
        );
        assert!(lines[1].contains(" seq=8 "));
        assert!(lines[1].ends_with(" message=next"));
        let tick = lines[0]
            .split(" monotonic_ms=")
            .nth(1)
            .unwrap()
            .split(' ')
            .next()
            .unwrap()
            .parse::<i64>()
            .unwrap();
        assert!(tick >= 0 && tick <= monotonic_ms().unwrap());
        std::fs::remove_file(path).unwrap();
        std::fs::remove_dir(dir).unwrap();
    }

    #[cfg(windows)]
    #[test]
    fn windows_phase_refuses_invalid_handle_and_input_before_reading_it() {
        let _environment = RUN_ID_ENV_LOCK.lock().unwrap();
        assert!(!unsafe { rt_phase_profile_record(-1, 0, b"x".as_ptr(), 1) });
        assert!(!unsafe { rt_phase_profile_record(0, 0, b"x".as_ptr(), 1) });
        assert!(!unsafe { rt_phase_profile_record(-1, 0, std::ptr::null(), 1) });
        assert!(!unsafe { rt_phase_profile_record(-1, 0, std::ptr::null(), -1) });
        // The oversized length is rejected without dereferencing this pointer.
        assert!(!unsafe {
            rt_phase_profile_record(
                -1,
                0,
                std::ptr::NonNull::<u8>::dangling().as_ptr(),
                TOKEN_CAP as i64 + 1,
            )
        });
    }

    #[cfg(windows)]
    #[test]
    fn windows_run_id_is_encoded_and_oversized_values_are_refused() {
        let _environment = RUN_ID_ENV_LOCK.lock().unwrap();
        let _restore = RestoreRunId(std::env::var_os("SIMPLE_EVIDENCE_RUN_ID"));
        // SAFETY: serialized provider tests only; the guard restores even on
        // assertion failure. The canonical test launch uses --test-threads=1.
        unsafe { std::env::set_var("SIMPLE_EVIDENCE_RUN_ID", "run α =%\r\n") };
        assert_eq!(run_id_token().unwrap().as_bytes(), "run%20α%20%3D%25%0D%0A".as_bytes());
        unsafe { std::env::set_var("SIMPLE_EVIDENCE_RUN_ID", "x".repeat(256)) };
        assert!(
            run_id_token().is_none(),
            "API capacity overflow must not become an unset sentinel"
        );
        unsafe { std::env::set_var("SIMPLE_EVIDENCE_RUN_ID", "%".repeat(86)) };
        assert!(run_id_token().is_none(), "escaped token overflow must be refused");
        unsafe { std::env::set_var("SIMPLE_EVIDENCE_RUN_ID", "α".repeat(129)) };
        assert!(run_id_token().is_none(), "UTF-8 expansion must obey the byte capacity");
        unsafe { std::env::set_var("SIMPLE_EVIDENCE_RUN_ID", "") };
        assert_eq!(run_id_token().unwrap().as_bytes(), b"-");
        unsafe { std::env::remove_var("SIMPLE_EVIDENCE_RUN_ID") };
        assert_eq!(run_id_token().unwrap().as_bytes(), b"-");
    }
}
