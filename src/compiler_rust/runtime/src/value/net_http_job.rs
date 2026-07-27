// Runtime-owned one-hop HTTP jobs. Workers only retain copied Rust data;
// RuntimeValue allocation stays on the polling/UI thread.

const BROWSER_HTTP_JOB_LIMIT: usize = 64;
const BROWSER_HTTP_RAW_LIMIT: usize = 50 * 1024 * 1024 + 64 * 1024;

struct BrowserHttpJob {
    canceled: std::sync::atomic::AtomicBool,
    socket: std::sync::Mutex<Option<TcpStream>>,
    outcome: std::sync::Mutex<Option<Result<Vec<u8>, String>>>,
}

lazy_static::lazy_static! {
    static ref BROWSER_HTTP_JOBS: std::sync::Mutex<HashMap<i64, std::sync::Arc<BrowserHttpJob>>> =
        std::sync::Mutex::new(HashMap::new());
}

static NEXT_BROWSER_HTTP_JOB: AtomicI64 = AtomicI64::new(1);
static LIVE_BROWSER_HTTP_JOBS: AtomicUsize = AtomicUsize::new(0);

fn browser_http_text(value: crate::value::RuntimeValue) -> Option<String> {
    let (ptr, len) = runtime_text_ptr_len(value)?;
    let bytes = unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };
    std::str::from_utf8(bytes).ok().map(str::to_owned)
}

fn browser_http_remaining(deadline: std::time::Instant) -> std::io::Result<Duration> {
    deadline
        .checked_duration_since(std::time::Instant::now())
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::TimedOut, "browser HTTP deadline exceeded"))
}

fn browser_http_canceled(job: &BrowserHttpJob) -> std::io::Result<()> {
    if job.canceled.load(Ordering::Acquire) {
        Err(std::io::Error::new(
            std::io::ErrorKind::Interrupted,
            "browser HTTP job canceled",
        ))
    } else {
        Ok(())
    }
}

fn browser_http_connect(
    host: &str,
    port: i64,
    deadline: std::time::Instant,
    job: &BrowserHttpJob,
) -> std::io::Result<TcpStream> {
    let authority = if host.contains(':') {
        format!("[{host}]:{port}")
    } else {
        format!("{host}:{port}")
    };
    let addresses = resolve_socket_addrs_with_timeout(authority, browser_http_remaining(deadline)?)?;
    let mut last_error = None;
    for address in addresses {
        browser_http_canceled(job)?;
        match TcpStream::connect_timeout(&address, browser_http_remaining(deadline)?) {
            Ok(stream) => {
                *job.socket.lock().unwrap() = stream.try_clone().ok();
                return Ok(stream);
            }
            Err(error) => last_error = Some(error),
        }
    }
    Err(last_error.unwrap_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::AddrNotAvailable,
            "browser HTTP target resolved to no addresses",
        )
    }))
}

fn browser_http_read_plain(
    stream: &mut TcpStream,
    deadline: std::time::Instant,
    job: &BrowserHttpJob,
) -> std::io::Result<Vec<u8>> {
    let mut response = Vec::new();
    let mut chunk = [0u8; 8192];
    loop {
        browser_http_canceled(job)?;
        stream.set_read_timeout(Some(browser_http_remaining(deadline)?))?;
        match stream.read(&mut chunk) {
            Ok(0) => return Ok(response),
            Ok(count) => {
                if response.len() > BROWSER_HTTP_RAW_LIMIT - count {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::OutOfMemory,
                        "browser HTTP response exceeds limit",
                    ));
                }
                response.extend_from_slice(&chunk[..count]);
            }
            Err(error) => return Err(error),
        }
    }
}

#[cfg(feature = "runtime-tls")]
fn browser_http_tls(
    host: &str,
    stream: TcpStream,
    request: &[u8],
    deadline: std::time::Instant,
    job: &BrowserHttpJob,
) -> std::io::Result<Vec<u8>> {
    let server_name = rustls::pki_types::ServerName::try_from(host.to_owned())
        .map_err(|_| std::io::Error::new(std::io::ErrorKind::InvalidInput, "invalid TLS server name"))?;
    let config = platform_tls_client_config()
        .map_err(|error| std::io::Error::new(std::io::ErrorKind::Other, error))?;
    let connection = rustls::ClientConnection::new(config, server_name)
        .map_err(|error| std::io::Error::new(std::io::ErrorKind::Other, error))?;
    let mut tls = rustls::StreamOwned::new(connection, stream);
    browser_http_canceled(job)?;
    tls.sock.set_write_timeout(Some(browser_http_remaining(deadline)?))?;
    tls.write_all(request)?;
    tls.flush()?;

    let mut response = Vec::new();
    let mut chunk = [0u8; 8192];
    loop {
        browser_http_canceled(job)?;
        tls.sock.set_read_timeout(Some(browser_http_remaining(deadline)?))?;
        match tls.read(&mut chunk) {
            Ok(0) => return Ok(response),
            Ok(count) => {
                if response.len() > BROWSER_HTTP_RAW_LIMIT - count {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::OutOfMemory,
                        "browser HTTPS response exceeds limit",
                    ));
                }
                response.extend_from_slice(&chunk[..count]);
            }
            Err(error) => return Err(error),
        }
    }
}

#[cfg(not(feature = "runtime-tls"))]
fn browser_http_tls(
    _host: &str,
    _stream: TcpStream,
    _request: &[u8],
    _deadline: std::time::Instant,
    _job: &BrowserHttpJob,
) -> std::io::Result<Vec<u8>> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "browser HTTPS requires runtime TLS",
    ))
}

fn browser_http_perform(
    scheme: &str,
    host: &str,
    port: i64,
    request: &[u8],
    timeout_ms: i64,
    job: &BrowserHttpJob,
) -> Result<Vec<u8>, String> {
    if (scheme != "http" && scheme != "https") || host.is_empty() || !(1..=65535).contains(&port) {
        return Err("invalid browser HTTP target".to_owned());
    }
    if request.len() > BROWSER_HTTP_RAW_LIMIT || timeout_ms <= 0 {
        return Err("invalid browser HTTP request limit".to_owned());
    }
    let deadline = std::time::Instant::now()
        .checked_add(Duration::from_millis(timeout_ms as u64))
        .ok_or_else(|| "invalid browser HTTP deadline".to_owned())?;
    let mut stream = browser_http_connect(host, port, deadline, job).map_err(|e| e.to_string())?;
    if scheme == "https" {
        return browser_http_tls(host, stream, request, deadline, job).map_err(|e| e.to_string());
    }
    browser_http_canceled(job).map_err(|e| e.to_string())?;
    stream
        .set_write_timeout(Some(browser_http_remaining(deadline).map_err(|e| e.to_string())?))
        .map_err(|e| e.to_string())?;
    stream.write_all(request).map_err(|e| e.to_string())?;
    stream.flush().map_err(|e| e.to_string())?;
    browser_http_read_plain(&mut stream, deadline, job).map_err(|e| e.to_string())
}

#[no_mangle]
pub extern "C" fn rt_browser_http_job_start(
    scheme: crate::value::RuntimeValue,
    host: crate::value::RuntimeValue,
    port: i64,
    request: crate::value::RuntimeValue,
    timeout_ms: i64,
) -> i64 {
    let Some(scheme) = browser_http_text(scheme) else {
        return -1;
    };
    let Some(host) = browser_http_text(host) else {
        return -1;
    };
    let Some(request) = runtime_byte_array_to_vec(request) else {
        return -1;
    };
    if LIVE_BROWSER_HTTP_JOBS.fetch_add(1, Ordering::AcqRel) >= BROWSER_HTTP_JOB_LIMIT {
        LIVE_BROWSER_HTTP_JOBS.fetch_sub(1, Ordering::AcqRel);
        return -1;
    }
    let mut jobs = BROWSER_HTTP_JOBS.lock().unwrap();
    let handle = NEXT_BROWSER_HTTP_JOB.fetch_add(1, Ordering::Relaxed);
    let job = std::sync::Arc::new(BrowserHttpJob {
        canceled: std::sync::atomic::AtomicBool::new(false),
        socket: std::sync::Mutex::new(None),
        outcome: std::sync::Mutex::new(None),
    });
    jobs.insert(handle, job.clone());
    drop(jobs);

    let spawned = std::thread::Builder::new()
        .name("simple-browser-http".to_owned())
        .spawn(move || {
            let outcome = browser_http_perform(&scheme, &host, port, &request, timeout_ms, &job);
            *job.socket.lock().unwrap() = None;
            *job.outcome.lock().unwrap() = Some(outcome);
            LIVE_BROWSER_HTTP_JOBS.fetch_sub(1, Ordering::AcqRel);
        });
    if spawned.is_err() {
        BROWSER_HTTP_JOBS.lock().unwrap().remove(&handle);
        LIVE_BROWSER_HTTP_JOBS.fetch_sub(1, Ordering::AcqRel);
        return -1;
    }
    handle
}

#[no_mangle]
pub extern "C" fn rt_browser_http_job_poll(handle: i64) -> i64 {
    let job = BROWSER_HTTP_JOBS.lock().unwrap().get(&handle).cloned();
    match job {
        Some(job) => {
            if job.outcome.lock().unwrap().is_some() {
                1
            } else {
                0
            }
        }
        None => -1,
    }
}

#[no_mangle]
pub extern "C" fn rt_browser_http_job_take_response(handle: i64) -> crate::value::RuntimeValue {
    let job = BROWSER_HTTP_JOBS.lock().unwrap().get(&handle).cloned();
    if let Some(job) = job {
        if let Some(Ok(bytes)) = job.outcome.lock().unwrap().as_ref() {
            return unsafe {
                crate::value::sffi::file_io::rt_bytes_from_raw(bytes.as_ptr() as i64, bytes.len() as i64)
            };
        }
    }
    crate::value::collections::rt_array_new(0)
}

#[no_mangle]
pub extern "C" fn rt_browser_http_job_take_error(handle: i64) -> crate::value::RuntimeValue {
    let job = BROWSER_HTTP_JOBS.lock().unwrap().get(&handle).cloned();
    if let Some(job) = job {
        if let Some(Err(error)) = job.outcome.lock().unwrap().as_ref() {
            return unsafe { crate::value::collections::rt_string_new(error.as_ptr(), error.len() as u64) };
        }
    }
    unsafe { crate::value::collections::rt_string_new(std::ptr::null(), 0) }
}

#[no_mangle]
pub extern "C" fn rt_browser_http_job_cancel(handle: i64) -> bool {
    if let Some(job) = BROWSER_HTTP_JOBS.lock().unwrap().get(&handle) {
        job.canceled.store(true, Ordering::Release);
        if let Some(socket) = job.socket.lock().unwrap().as_ref() {
            let _ = socket.shutdown(std::net::Shutdown::Both);
        }
        return true;
    }
    false
}

#[no_mangle]
pub extern "C" fn rt_browser_http_job_free(handle: i64) -> bool {
    let job = BROWSER_HTTP_JOBS.lock().unwrap().remove(&handle);
    if let Some(job) = job {
        job.canceled.store(true, Ordering::Release);
        if let Some(socket) = job.socket.lock().unwrap().as_ref() {
            let _ = socket.shutdown(std::net::Shutdown::Both);
        }
        return true;
    }
    false
}
