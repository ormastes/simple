// Runtime-owned one-hop HTTP jobs. Workers only retain copied Rust data;
// RuntimeValue allocation stays on the polling/UI thread.

const BROWSER_HTTP_JOB_LIMIT: usize = 64;
const BROWSER_HTTP_RAW_LIMIT: usize = 50 * 1024 * 1024 + 64 * 1024;
const BROWSER_HTTP_NETWORK_ERROR: &str = "network: Network request failed";
const BROWSER_HTTP_NETWORK_TIMEOUT: &str = "network-timeout: Network request timed out";
const BROWSER_HTTP_TLS_CERTIFICATE: &str = "tls-certificate: TLS certificate validation failed";
const BROWSER_HTTP_TLS_HOSTNAME: &str = "tls-hostname: TLS certificate identity validation failed";
const BROWSER_HTTP_TLS_PROTOCOL: &str = "tls-protocol: TLS protocol negotiation failed";
const BROWSER_HTTP_TLS_TIMEOUT: &str = "tls-timeout: TLS connection timed out";

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

fn browser_http_network_error(error: &std::io::Error) -> String {
    if error.kind() == std::io::ErrorKind::TimedOut || error.kind() == std::io::ErrorKind::WouldBlock {
        BROWSER_HTTP_NETWORK_TIMEOUT.to_owned()
    } else {
        BROWSER_HTTP_NETWORK_ERROR.to_owned()
    }
}

#[cfg(feature = "runtime-tls")]
fn browser_http_tls_error(error: &std::io::Error) -> String {
    if error.kind() == std::io::ErrorKind::TimedOut || error.kind() == std::io::ErrorKind::WouldBlock {
        return BROWSER_HTTP_TLS_TIMEOUT.to_owned();
    }
    if error.kind() == std::io::ErrorKind::Interrupted || error.kind() == std::io::ErrorKind::OutOfMemory {
        return BROWSER_HTTP_NETWORK_ERROR.to_owned();
    }
    match error
        .get_ref()
        .and_then(|source| source.downcast_ref::<rustls::Error>())
    {
        Some(rustls::Error::InvalidCertificate(
            rustls::CertificateError::NotValidForName | rustls::CertificateError::NotValidForNameContext { .. },
        )) => BROWSER_HTTP_TLS_HOSTNAME.to_owned(),
        Some(rustls::Error::InvalidCertificate(_)) => BROWSER_HTTP_TLS_CERTIFICATE.to_owned(),
        Some(_) => BROWSER_HTTP_TLS_PROTOCOL.to_owned(),
        None => BROWSER_HTTP_NETWORK_ERROR.to_owned(),
    }
}

fn browser_http_connect(
    host: &str,
    port: i64,
    deadline: std::time::Instant,
    job: &BrowserHttpJob,
    public_only: bool,
) -> std::io::Result<TcpStream> {
    let authority = if host.contains(':') {
        format!("[{host}]:{port}")
    } else {
        format!("{host}:{port}")
    };
    let addresses = resolve_socket_addrs_with_timeout(authority, browser_http_remaining(deadline)?)?;
    if public_only && !browser_http_resolved_addresses_are_public(&addresses) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            "browser HTTP target resolved to a non-public address",
        ));
    }
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

fn browser_http_ipv4_in(address: Ipv4Addr, network: [u8; 4], prefix: u32) -> bool {
    let address = u32::from(address);
    let network = u32::from_be_bytes(network);
    let mask = if prefix == 0 { 0 } else { u32::MAX << (32 - prefix) };
    address & mask == network & mask
}

fn browser_http_ipv6_in(address: Ipv6Addr, network: [u16; 8], prefix: u32) -> bool {
    let address = u128::from(address);
    let network = network
        .iter()
        .fold(0u128, |value, segment| (value << 16) | u128::from(*segment));
    let mask = if prefix == 0 { 0 } else { u128::MAX << (128 - prefix) };
    address & mask == network & mask
}

fn browser_http_address_is_public(address: std::net::IpAddr) -> bool {
    match address {
        std::net::IpAddr::V4(address) => ![
            ([0, 0, 0, 0], 8),
            ([10, 0, 0, 0], 8),
            ([100, 64, 0, 0], 10),
            ([127, 0, 0, 0], 8),
            ([169, 254, 0, 0], 16),
            ([172, 16, 0, 0], 12),
            ([192, 0, 0, 0], 24),
            ([192, 0, 2, 0], 24),
            ([192, 88, 99, 0], 24),
            ([192, 168, 0, 0], 16),
            ([198, 18, 0, 0], 15),
            ([198, 51, 100, 0], 24),
            ([203, 0, 113, 0], 24),
            ([224, 0, 0, 0], 4),
            ([240, 0, 0, 0], 4),
        ]
        .iter()
        .any(|(network, prefix)| browser_http_ipv4_in(address, *network, *prefix)),
        std::net::IpAddr::V6(address) => {
            if address.to_ipv4_mapped().is_some() || !browser_http_ipv6_in(address, [0x2000, 0, 0, 0, 0, 0, 0, 0], 3) {
                return false;
            }
            ![
                ([0x2001, 0, 0, 0, 0, 0, 0, 0], 23),
                ([0x2001, 0x0db8, 0, 0, 0, 0, 0, 0], 32),
                ([0x2002, 0, 0, 0, 0, 0, 0, 0], 16),
                ([0x3fff, 0, 0, 0, 0, 0, 0, 0], 20),
            ]
            .iter()
            .any(|(network, prefix)| browser_http_ipv6_in(address, *network, *prefix))
        }
    }
}

fn browser_http_resolved_addresses_are_public(addresses: &[SocketAddr]) -> bool {
    addresses
        .iter()
        .all(|address| browser_http_address_is_public(address.ip()))
}

fn browser_http_extend_response(
    response: &mut Vec<u8>,
    chunk: &[u8],
    max_response_bytes: usize,
    scheme: &str,
) -> std::io::Result<()> {
    if response.len() > max_response_bytes.saturating_sub(chunk.len()) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::OutOfMemory,
            format!("browser {scheme} response exceeds limit"),
        ));
    }
    response.extend_from_slice(chunk);
    Ok(())
}

fn browser_http_read_plain(
    stream: &mut TcpStream,
    deadline: std::time::Instant,
    job: &BrowserHttpJob,
    max_response_bytes: usize,
) -> std::io::Result<Vec<u8>> {
    let mut response = Vec::new();
    let mut chunk = [0u8; 8192];
    loop {
        browser_http_canceled(job)?;
        stream.set_read_timeout(Some(browser_http_remaining(deadline)?))?;
        match stream.read(&mut chunk) {
            Ok(0) => return Ok(response),
            Ok(count) => {
                browser_http_extend_response(&mut response, &chunk[..count], max_response_bytes, "HTTP")?;
            }
            Err(error) => return Err(error),
        }
    }
}

#[cfg(feature = "runtime-tls")]
struct BrowserHttpDeadlineStream {
    stream: TcpStream,
    deadline: std::time::Instant,
}

#[cfg(feature = "runtime-tls")]
impl BrowserHttpDeadlineStream {
    fn new(stream: TcpStream, deadline: std::time::Instant) -> Self {
        Self { stream, deadline }
    }

    fn refresh_timeouts(&self) -> std::io::Result<()> {
        let remaining = browser_http_remaining(self.deadline)?;
        self.stream.set_read_timeout(Some(remaining))?;
        self.stream.set_write_timeout(Some(remaining))
    }
}

#[cfg(feature = "runtime-tls")]
impl std::io::Read for BrowserHttpDeadlineStream {
    fn read(&mut self, buffer: &mut [u8]) -> std::io::Result<usize> {
        self.stream
            .set_read_timeout(Some(browser_http_remaining(self.deadline)?))?;
        std::io::Read::read(&mut self.stream, buffer)
    }
}

#[cfg(feature = "runtime-tls")]
impl std::io::Write for BrowserHttpDeadlineStream {
    fn write(&mut self, buffer: &[u8]) -> std::io::Result<usize> {
        self.stream
            .set_write_timeout(Some(browser_http_remaining(self.deadline)?))?;
        std::io::Write::write(&mut self.stream, buffer)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.stream
            .set_write_timeout(Some(browser_http_remaining(self.deadline)?))?;
        std::io::Write::flush(&mut self.stream)
    }
}

#[cfg(feature = "runtime-tls")]
fn browser_http_tls(
    host: &str,
    stream: TcpStream,
    request: &[u8],
    deadline: std::time::Instant,
    job: &BrowserHttpJob,
    max_response_bytes: usize,
) -> Result<Vec<u8>, String> {
    let server_name =
        rustls::pki_types::ServerName::try_from(host.to_owned()).map_err(|_| BROWSER_HTTP_TLS_HOSTNAME.to_owned())?;
    let config = platform_tls_client_config().map_err(|_| BROWSER_HTTP_TLS_PROTOCOL.to_owned())?;
    let connection =
        rustls::ClientConnection::new(config, server_name).map_err(|_| BROWSER_HTTP_TLS_PROTOCOL.to_owned())?;
    let mut tls = rustls::StreamOwned::new(connection, BrowserHttpDeadlineStream::new(stream, deadline));
    browser_http_canceled(job).map_err(|error| browser_http_tls_error(&error))?;
    tls.sock
        .refresh_timeouts()
        .map_err(|error| browser_http_tls_error(&error))?;
    tls.write_all(request).map_err(|error| browser_http_tls_error(&error))?;
    tls.sock
        .refresh_timeouts()
        .map_err(|error| browser_http_tls_error(&error))?;
    tls.flush().map_err(|error| browser_http_tls_error(&error))?;

    let mut response = Vec::new();
    let mut chunk = [0u8; 8192];
    loop {
        browser_http_canceled(job).map_err(|error| browser_http_tls_error(&error))?;
        match tls.read(&mut chunk) {
            Ok(0) => return Ok(response),
            Ok(count) => {
                browser_http_extend_response(&mut response, &chunk[..count], max_response_bytes, "HTTPS")
                    .map_err(|error| browser_http_tls_error(&error))?;
            }
            Err(error) => return Err(browser_http_tls_error(&error)),
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
    _max_response_bytes: usize,
) -> Result<Vec<u8>, String> {
    Err(BROWSER_HTTP_TLS_PROTOCOL.to_owned())
}

fn browser_http_perform(
    scheme: &str,
    host: &str,
    port: i64,
    request: &[u8],
    timeout_ms: i64,
    job: &BrowserHttpJob,
    max_response_bytes: usize,
    public_only: bool,
) -> Result<Vec<u8>, String> {
    if (scheme != "http" && scheme != "https") || host.is_empty() || !(1..=65535).contains(&port) {
        return Err("invalid browser HTTP target".to_owned());
    }
    if request.len() > BROWSER_HTTP_RAW_LIMIT
        || timeout_ms <= 0
        || max_response_bytes == 0
        || max_response_bytes > BROWSER_HTTP_RAW_LIMIT
    {
        return Err("invalid browser HTTP request limit".to_owned());
    }
    let deadline = std::time::Instant::now()
        .checked_add(Duration::from_millis(timeout_ms as u64))
        .ok_or_else(|| "invalid browser HTTP deadline".to_owned())?;
    let mut stream = browser_http_connect(host, port, deadline, job, public_only)
        .map_err(|error| browser_http_network_error(&error))?;
    if scheme == "https" {
        return browser_http_tls(host, stream, request, deadline, job, max_response_bytes);
    }
    browser_http_canceled(job).map_err(|error| browser_http_network_error(&error))?;
    stream
        .set_write_timeout(Some(
            browser_http_remaining(deadline).map_err(|error| browser_http_network_error(&error))?,
        ))
        .map_err(|error| browser_http_network_error(&error))?;
    stream
        .write_all(request)
        .map_err(|error| browser_http_network_error(&error))?;
    stream.flush().map_err(|error| browser_http_network_error(&error))?;
    browser_http_read_plain(&mut stream, deadline, job, max_response_bytes)
        .map_err(|error| browser_http_network_error(&error))
}

#[cfg(all(test, feature = "runtime-tls"))]
mod browser_http_failure_tests {
    use super::*;

    #[test]
    fn classifies_tls_failures_without_platform_detail() {
        let hostname = std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            rustls::Error::InvalidCertificate(rustls::CertificateError::NotValidForName),
        );
        let certificate = std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            rustls::Error::InvalidCertificate(rustls::CertificateError::Expired),
        );
        let protocol = std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            rustls::Error::General("private platform detail".to_owned()),
        );
        let timeout = std::io::Error::new(std::io::ErrorKind::TimedOut, "private timeout detail");
        let unix_timeout = std::io::Error::new(std::io::ErrorKind::WouldBlock, "private timeout detail");
        let response_limit =
            std::io::Error::new(std::io::ErrorKind::InvalidData, "browser HTTPS response exceeds limit");

        assert_eq!(browser_http_tls_error(&hostname), BROWSER_HTTP_TLS_HOSTNAME);
        assert_eq!(browser_http_tls_error(&certificate), BROWSER_HTTP_TLS_CERTIFICATE);
        assert_eq!(browser_http_tls_error(&protocol), BROWSER_HTTP_TLS_PROTOCOL);
        assert_eq!(browser_http_tls_error(&timeout), BROWSER_HTTP_TLS_TIMEOUT);
        assert_eq!(browser_http_tls_error(&unix_timeout), BROWSER_HTTP_TLS_TIMEOUT);
        assert_eq!(browser_http_tls_error(&response_limit), BROWSER_HTTP_NETWORK_ERROR);
    }

    #[test]
    fn classifies_network_failures_without_platform_detail() {
        let failed = std::io::Error::new(std::io::ErrorKind::ConnectionRefused, "private address detail");
        let timeout = std::io::Error::new(std::io::ErrorKind::TimedOut, "private timeout detail");
        let unix_timeout = std::io::Error::new(std::io::ErrorKind::WouldBlock, "private timeout detail");

        assert_eq!(browser_http_network_error(&failed), BROWSER_HTTP_NETWORK_ERROR);
        assert_eq!(browser_http_network_error(&timeout), BROWSER_HTTP_NETWORK_TIMEOUT);
        assert_eq!(browser_http_network_error(&unix_timeout), BROWSER_HTTP_NETWORK_TIMEOUT);
    }
}

fn browser_http_job_start(
    scheme: crate::value::RuntimeValue,
    host: crate::value::RuntimeValue,
    port: i64,
    request: crate::value::RuntimeValue,
    timeout_ms: i64,
    max_response_bytes: i64,
    public_only: bool,
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
    let Ok(max_response_bytes) = usize::try_from(max_response_bytes) else {
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
            let outcome = browser_http_perform(
                &scheme,
                &host,
                port,
                &request,
                timeout_ms,
                &job,
                max_response_bytes,
                public_only,
            );
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
pub extern "C" fn rt_browser_http_job_start(
    scheme: crate::value::RuntimeValue,
    host: crate::value::RuntimeValue,
    port: i64,
    request: crate::value::RuntimeValue,
    timeout_ms: i64,
) -> i64 {
    browser_http_job_start(
        scheme,
        host,
        port,
        request,
        timeout_ms,
        BROWSER_HTTP_RAW_LIMIT as i64,
        false,
    )
}

#[no_mangle]
pub extern "C" fn rt_browser_http_job_start_public_limited(
    scheme: crate::value::RuntimeValue,
    host: crate::value::RuntimeValue,
    port: i64,
    request: crate::value::RuntimeValue,
    timeout_ms: i64,
    max_response_bytes: i64,
) -> i64 {
    browser_http_job_start(scheme, host, port, request, timeout_ms, max_response_bytes, true)
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

#[cfg(test)]
mod browser_http_job_tests {
    use super::*;

    #[cfg(feature = "runtime-tls")]
    #[test]
    fn silent_tls_peer_respects_job_deadline_and_retires_slot() {
        let listener = std::net::TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let port = listener.local_addr().unwrap().port();
        let (release_tx, release_rx) = std::sync::mpsc::channel();
        let server = std::thread::spawn(move || {
            let (_stream, _) = listener.accept().unwrap();
            let _ = release_rx.recv_timeout(Duration::from_secs(1));
        });
        let text_value = |value: &str| crate::value::collections::rt_string_new(value.as_ptr(), value.len() as u64);
        let request = b"GET / HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n";
        let request_value =
            unsafe { crate::value::sffi::file_io::rt_bytes_from_raw(request.as_ptr() as i64, request.len() as i64) };
        let live_before = LIVE_BROWSER_HTTP_JOBS.load(Ordering::Acquire);
        let started = std::time::Instant::now();
        let handle = browser_http_job_start(
            text_value("https"),
            text_value("127.0.0.1"),
            i64::from(port),
            request_value,
            50,
            4096,
            false,
        );
        assert!(handle > 0);
        while rt_browser_http_job_poll(handle) == 0 && started.elapsed() < Duration::from_millis(500) {
            std::thread::yield_now();
        }
        let terminal = rt_browser_http_job_poll(handle);
        let terminal_elapsed = started.elapsed();
        let _ = release_tx.send(());
        server.join().unwrap();

        assert_eq!(terminal, 1, "silent TLS peer outlived the job deadline");
        assert!(terminal_elapsed >= Duration::from_millis(25));
        assert!(terminal_elapsed < Duration::from_millis(500));
        assert!(runtime_byte_array_to_vec(rt_browser_http_job_take_response(handle))
            .unwrap()
            .is_empty());
        let error = browser_http_text(rt_browser_http_job_take_error(handle))
            .unwrap()
            .to_lowercase();
        assert!(
            error.contains("timed out")
                || error.contains("would block")
                || error.contains("temporarily unavailable")
                || error.contains("deadline exceeded")
                || error.contains("failed to respond")
                || error.contains("did not properly respond")
                || error.contains("os error 10060"),
            "silent TLS peer failed for a non-timeout reason: {error}"
        );
        assert!(rt_browser_http_job_free(handle));
        while LIVE_BROWSER_HTTP_JOBS.load(Ordering::Acquire) != live_before
            && started.elapsed() < Duration::from_millis(500)
        {
            std::thread::yield_now();
        }
        assert_eq!(LIVE_BROWSER_HTTP_JOBS.load(Ordering::Acquire), live_before);
    }

    #[test]
    fn public_address_policy_rejects_non_public_ipv4_and_ipv6() {
        for address in [
            "0.0.0.0",
            "10.0.0.1",
            "100.64.0.1",
            "127.0.0.1",
            "169.254.1.1",
            "172.16.0.1",
            "192.0.2.1",
            "192.168.1.1",
            "198.18.0.1",
            "198.51.100.1",
            "203.0.113.1",
            "224.0.0.1",
            "240.0.0.1",
            "::",
            "::1",
            "::ffff:127.0.0.1",
            "::ffff:8.8.8.8",
            "64:ff9b:1::1",
            "5f00::1",
            "100::1",
            "2001:db8::1",
            "2002::1",
            "3fff::1",
            "fc00::1",
            "fe80::1",
            "fec0::1",
            "ff00::1",
        ] {
            assert!(!browser_http_address_is_public(address.parse().unwrap()), "{address}");
        }
        for address in ["1.1.1.1", "8.8.8.8", "2606:4700:4700::1111", "2001:4860:4860::8888"] {
            assert!(browser_http_address_is_public(address.parse().unwrap()), "{address}");
        }
    }

    #[test]
    fn public_address_policy_rejects_any_mixed_resolution_set() {
        let address = |value: &str| value.parse::<SocketAddr>().unwrap();

        assert!(browser_http_resolved_addresses_are_public(&[]));
        assert!(browser_http_resolved_addresses_are_public(&[
            address("1.1.1.1:443"),
            address("[2606:4700:4700::1111]:443"),
        ]));
        assert!(!browser_http_resolved_addresses_are_public(&[
            address("1.1.1.1:443"),
            address("127.0.0.1:443"),
        ]));
    }

    #[test]
    fn requested_response_cap_is_exact() {
        let mut response = Vec::new();
        browser_http_extend_response(&mut response, b"1234", 5, "HTTP").unwrap();
        browser_http_extend_response(&mut response, b"5", 5, "HTTPS").unwrap();
        assert_eq!(response, b"12345");
        let error = browser_http_extend_response(&mut response, b"6", 5, "HTTP").unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::OutOfMemory);
        assert_eq!(response, b"12345");
    }
}
