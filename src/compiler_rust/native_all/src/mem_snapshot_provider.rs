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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_encoding_is_bounded_and_schema_safe() {
        let token = encode_token::<32>(b"a b=c%\r\n").unwrap();
        assert_eq!(token.as_bytes(), b"a%20b%3Dc%25%0D%0A");
        assert!(encode_token::<2>(b" ").is_none());
    }
}
