//! Serial port FFI functions for POSIX tty devices.
//!
//! Opens `/dev/ttyUSB*`, `/dev/ttyS*`, `/dev/cu.*` etc. with configurable
//! baud rate and raw (no-echo, no-CRLF) mode. Returns raw file descriptors
//! as i64 handles. Caller is responsible for closing.
//!
//! Only compiled on Unix; all functions return error values on non-Unix.

#[cfg(unix)]
use nix::sys::termios::{
    cfsetispeed, cfsetospeed, tcsetattr, BaudRate, SetArg, InputFlags, LocalFlags, OutputFlags, ControlFlags,
};
#[cfg(unix)]
use std::os::unix::io::{BorrowedFd, FromRawFd, OwnedFd};
use crate::value::RuntimeValue;

/// Open a serial device at the given baud rate in raw mode.
/// Returns fd (> 0) on success, 0 on failure.
#[no_mangle]
pub extern "C" fn rt_serial_open(device: RuntimeValue, baud: i64) -> i64 {
    #[cfg(unix)]
    {
        let dev = match runtime_value_to_string(device) {
            Some(s) => s,
            None => return 0,
        };

        let dev_c = match std::ffi::CString::new(dev.as_str()) {
            Ok(c) => c,
            Err(_) => return 0,
        };

        let fd = unsafe { libc::open(dev_c.as_ptr(), libc::O_RDWR | libc::O_NOCTTY | libc::O_NONBLOCK) };

        if fd < 0 {
            let err = std::io::Error::last_os_error();
            eprintln!("rt_serial_open: open({}) failed: {}", dev, err);
            return 0;
        }

        // Restore blocking mode
        unsafe {
            let flags = libc::fcntl(fd, libc::F_GETFL);
            if flags >= 0 {
                let _ = libc::fcntl(fd, libc::F_SETFL, flags & !libc::O_NONBLOCK);
            }
        }

        // Configure termios: raw mode at specified baud rate
        let baud_rate = int_to_baud(baud);
        let owned = unsafe { OwnedFd::from_raw_fd(fd) };
        if let Err(e) = configure_serial(&owned, baud_rate) {
            eprintln!("rt_serial_open: configure_serial failed: {}", e);
            // fd is closed when owned drops
            return 0;
        }

        // Leak the OwnedFd — caller manages the fd lifetime
        let raw = {
            use std::os::unix::io::IntoRawFd;
            owned.into_raw_fd()
        };
        raw as i64
    }

    #[cfg(not(unix))]
    {
        let _ = (device, baud);
        eprintln!("rt_serial_open: serial ports not supported on this platform");
        0
    }
}

/// Close a serial port fd. Returns true on success.
#[no_mangle]
pub extern "C" fn rt_serial_close(fd: i64) -> RuntimeValue {
    #[cfg(unix)]
    {
        let ok = unsafe { libc::close(fd as libc::c_int) == 0 };
        if !ok {
            eprintln!("rt_serial_close: {}", std::io::Error::last_os_error());
        }
        RuntimeValue::from_bool(ok)
    }

    #[cfg(not(unix))]
    {
        let _ = fd;
        RuntimeValue::from_bool(false)
    }
}

/// Read up to max_bytes from a serial port. Blocks until data arrives or timeout.
/// Returns the bytes as a text string (raw bytes — binary-safe via UTF-8 lossy).
#[no_mangle]
pub extern "C" fn rt_serial_read(fd: i64, max_bytes: i64) -> RuntimeValue {
    #[cfg(unix)]
    {
        use std::time::{Duration, Instant};

        let fd_raw = fd as libc::c_int;
        let cap = max_bytes.clamp(1, 65536) as usize;
        let mut buf = vec![0u8; cap];
        let timeout = Duration::from_secs(5); // default 5s read timeout
        let start = Instant::now();

        loop {
            let n = unsafe { libc::read(fd_raw, buf.as_mut_ptr() as *mut libc::c_void, cap) };

            if n > 0 {
                let text = String::from_utf8_lossy(&buf[..n as usize]);
                return string_to_runtime_value(&text);
            } else if n == 0 {
                return string_to_runtime_value("");
            } else {
                let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
                if errno == libc::EAGAIN as i32 || errno == libc::EWOULDBLOCK as i32 {
                    if start.elapsed() >= timeout {
                        return string_to_runtime_value("");
                    }
                    std::thread::sleep(Duration::from_millis(10));
                } else {
                    eprintln!("rt_serial_read: {}", std::io::Error::last_os_error());
                    return string_to_runtime_value("");
                }
            }
        }
    }

    #[cfg(not(unix))]
    {
        let _ = (fd, max_bytes);
        string_to_runtime_value("")
    }
}

/// Write data to a serial port. Returns number of bytes written (0 on error).
#[no_mangle]
pub extern "C" fn rt_serial_write(fd: i64, data: RuntimeValue) -> i64 {
    #[cfg(unix)]
    {
        let text = match runtime_value_to_string(data) {
            Some(s) => s,
            None => return 0,
        };

        let n = unsafe { libc::write(fd as libc::c_int, text.as_ptr() as *const libc::c_void, text.len()) };

        if n < 0 {
            eprintln!("rt_serial_write: {}", std::io::Error::last_os_error());
            0
        } else {
            n as i64
        }
    }

    #[cfg(not(unix))]
    {
        let _ = (fd, data);
        0
    }
}

/// Set read timeout in milliseconds using VMIN/VTIME. Returns true on success.
/// timeout_ms == 0 → non-blocking; timeout_ms < 0 → blocking forever.
#[no_mangle]
pub extern "C" fn rt_serial_set_timeout(fd: i64, timeout_ms: i64) -> RuntimeValue {
    #[cfg(unix)]
    {
        use nix::sys::termios::{tcgetattr, tcsetattr, SetArg};
        let borrowed = unsafe { BorrowedFd::borrow_raw(fd as i32) };
        match tcgetattr(borrowed) {
            Ok(mut tios) => {
                if timeout_ms < 0 {
                    tios.control_chars[nix::sys::termios::SpecialCharacterIndices::VMIN as usize] = 1;
                    tios.control_chars[nix::sys::termios::SpecialCharacterIndices::VTIME as usize] = 0;
                } else if timeout_ms == 0 {
                    tios.control_chars[nix::sys::termios::SpecialCharacterIndices::VMIN as usize] = 0;
                    tios.control_chars[nix::sys::termios::SpecialCharacterIndices::VTIME as usize] = 0;
                } else {
                    let vtime = (timeout_ms / 100).clamp(1, 255) as u8;
                    tios.control_chars[nix::sys::termios::SpecialCharacterIndices::VMIN as usize] = 0;
                    tios.control_chars[nix::sys::termios::SpecialCharacterIndices::VTIME as usize] = vtime;
                }
                let ok = tcsetattr(borrowed, SetArg::TCSANOW, &tios).is_ok();
                RuntimeValue::from_bool(ok)
            }
            Err(e) => {
                eprintln!("rt_serial_set_timeout: tcgetattr failed: {}", e);
                RuntimeValue::from_bool(false)
            }
        }
    }

    #[cfg(not(unix))]
    {
        let _ = (fd, timeout_ms);
        RuntimeValue::from_bool(false)
    }
}

/// Flush (drain) the serial port output buffer. Returns true on success.
#[no_mangle]
pub extern "C" fn rt_serial_flush(fd: i64) -> RuntimeValue {
    #[cfg(unix)]
    {
        use nix::sys::termios::tcdrain;
        let borrowed = unsafe { BorrowedFd::borrow_raw(fd as i32) };
        let ok = tcdrain(borrowed).is_ok();
        RuntimeValue::from_bool(ok)
    }

    #[cfg(not(unix))]
    {
        let _ = fd;
        RuntimeValue::from_bool(false)
    }
}

/// Bidirectional relay: stdin (fd 0) ↔ serial fd.
/// Blocks until either end closes. Used by serial_proxy as SSH ProxyCommand.
/// Returns true on clean exit, false on I/O error.
#[no_mangle]
pub extern "C" fn rt_serial_relay(serial_fd: i64) -> RuntimeValue {
    #[cfg(unix)]
    {
        let sfd = serial_fd as libc::c_int;
        let stdin_fd: libc::c_int = 0;
        let stdout_fd: libc::c_int = 1;
        let mut buf = vec![0u8; 4096];

        loop {
            // poll both stdin and serial fd for readability
            let mut fds = [
                libc::pollfd {
                    fd: stdin_fd,
                    events: libc::POLLIN,
                    revents: 0,
                },
                libc::pollfd {
                    fd: sfd,
                    events: libc::POLLIN,
                    revents: 0,
                },
            ];

            let ret = unsafe { libc::poll(fds.as_mut_ptr(), 2, -1) };
            if ret < 0 {
                let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
                if errno == libc::EINTR as i32 {
                    continue;
                }
                eprintln!("rt_serial_relay: poll error: {}", std::io::Error::last_os_error());
                return RuntimeValue::from_bool(false);
            }

            // stdin → serial
            if fds[0].revents & libc::POLLIN != 0 {
                let n = unsafe { libc::read(stdin_fd, buf.as_mut_ptr() as *mut libc::c_void, buf.len()) };
                if n <= 0 {
                    break; // EOF on stdin → done
                }
                let mut written = 0usize;
                while written < n as usize {
                    let w = unsafe {
                        libc::write(
                            sfd,
                            buf[written..].as_ptr() as *const libc::c_void,
                            n as usize - written,
                        )
                    };
                    if w <= 0 {
                        eprintln!("rt_serial_relay: write to serial failed");
                        return RuntimeValue::from_bool(false);
                    }
                    written += w as usize;
                }
            } else if fds[0].revents & (libc::POLLHUP | libc::POLLERR) != 0 {
                break;
            }

            // serial → stdout
            if fds[1].revents & libc::POLLIN != 0 {
                let n = unsafe { libc::read(sfd, buf.as_mut_ptr() as *mut libc::c_void, buf.len()) };
                if n <= 0 {
                    break; // EOF on serial → done
                }
                let mut written = 0usize;
                while written < n as usize {
                    let w = unsafe {
                        libc::write(
                            stdout_fd,
                            buf[written..].as_ptr() as *const libc::c_void,
                            n as usize - written,
                        )
                    };
                    if w <= 0 {
                        eprintln!("rt_serial_relay: write to stdout failed");
                        return RuntimeValue::from_bool(false);
                    }
                    written += w as usize;
                }
            } else if fds[1].revents & (libc::POLLHUP | libc::POLLERR) != 0 {
                break;
            }
        }

        RuntimeValue::from_bool(true)
    }

    #[cfg(not(unix))]
    {
        let _ = serial_fd;
        eprintln!("rt_serial_relay: not supported on this platform");
        RuntimeValue::from_bool(false)
    }
}

// ============================================================================
// Internal helpers
// ============================================================================

fn string_to_runtime_value(s: &str) -> RuntimeValue {
    super::collections::rt_string_new(s.as_ptr(), s.len() as u64)
}

fn runtime_value_to_string(val: RuntimeValue) -> Option<String> {
    if !val.is_heap() {
        return None;
    }
    let ptr = val.as_heap_ptr() as *const super::collections::RuntimeString;
    if ptr.is_null() {
        return None;
    }
    unsafe {
        let s = &*ptr;
        let bytes = s.as_bytes();
        String::from_utf8(bytes.to_vec()).ok()
    }
}

#[cfg(unix)]
fn int_to_baud(baud: i64) -> BaudRate {
    match baud {
        50 => BaudRate::B50,
        75 => BaudRate::B75,
        110 => BaudRate::B110,
        134 => BaudRate::B134,
        150 => BaudRate::B150,
        200 => BaudRate::B200,
        300 => BaudRate::B300,
        600 => BaudRate::B600,
        1200 => BaudRate::B1200,
        1800 => BaudRate::B1800,
        2400 => BaudRate::B2400,
        4800 => BaudRate::B4800,
        9600 => BaudRate::B9600,
        19200 => BaudRate::B19200,
        38400 => BaudRate::B38400,
        57600 => BaudRate::B57600,
        115200 => BaudRate::B115200,
        230400 => BaudRate::B230400,
        _ => {
            eprintln!("rt_serial_open: unsupported baud rate {}, defaulting to 115200", baud);
            BaudRate::B115200
        }
    }
}

#[cfg(unix)]
fn configure_serial(fd: &OwnedFd, baud: BaudRate) -> nix::Result<()> {
    use nix::sys::termios::tcgetattr;

    let mut tios = tcgetattr(fd)?;

    // Raw mode: no echo, no line editing, no special char processing
    tios.input_flags &= !(InputFlags::IGNBRK
        | InputFlags::BRKINT
        | InputFlags::PARMRK
        | InputFlags::ISTRIP
        | InputFlags::INLCR
        | InputFlags::IGNCR
        | InputFlags::ICRNL
        | InputFlags::IXON);
    tios.output_flags &= !OutputFlags::OPOST;
    tios.local_flags &=
        !(LocalFlags::ECHO | LocalFlags::ECHONL | LocalFlags::ICANON | LocalFlags::ISIG | LocalFlags::IEXTEN);
    tios.control_flags &= !(ControlFlags::CSIZE | ControlFlags::PARENB);
    tios.control_flags |= ControlFlags::CS8 | ControlFlags::CREAD | ControlFlags::CLOCAL;

    // VMIN=1 VTIME=0: block until at least 1 char received
    tios.control_chars[nix::sys::termios::SpecialCharacterIndices::VMIN as usize] = 1;
    tios.control_chars[nix::sys::termios::SpecialCharacterIndices::VTIME as usize] = 0;

    cfsetispeed(&mut tios, baud)?;
    cfsetospeed(&mut tios, baud)?;
    tcsetattr(fd, SetArg::TCSANOW, &tios)?;
    Ok(())
}
