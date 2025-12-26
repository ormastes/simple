// HTTP FFI functions for runtime/value/net module

/// HTTP request structure passed from Simple code
/// This is a simplified representation - the actual parsing happens in this function
#[repr(C)]
pub struct HttpRequestData {
    pub method: i64,       // 0=GET, 1=POST, 2=PUT, 3=DELETE, 4=PATCH, 5=HEAD
    pub url_ptr: i64,      // Pointer to URL string
    pub url_len: i64,      // Length of URL string
    pub body_ptr: i64,     // Pointer to body bytes (0 if no body)
    pub body_len: i64,     // Length of body
    pub headers_ptr: i64,  // Pointer to headers array
    pub headers_count: i64, // Number of header pairs
}

/// Send an HTTP request.
/// Returns (response_ptr, error_code)
/// Response is a RuntimeValue containing the response data
#[no_mangle]
pub unsafe extern "C" fn native_http_send(request_ptr: i64, timeout_ns: i64) -> (i64, i64) {
    // Parse the URL from the request
    if request_ptr == 0 {
        return (0, NetError::InvalidInput as i64);
    }

    let req_data = &*(request_ptr as *const HttpRequestData);

    // Parse URL
    if req_data.url_ptr == 0 || req_data.url_len <= 0 {
        return (0, NetError::HttpInvalidUrl as i64);
    }
    let url_slice =
        std::slice::from_raw_parts(req_data.url_ptr as *const u8, req_data.url_len as usize);
    let url_str = match std::str::from_utf8(url_slice) {
        Ok(s) => s,
        Err(_) => return (0, NetError::HttpInvalidUrl as i64),
    };

    // Build the request
    let method = match req_data.method {
        0 => "GET",
        1 => "POST",
        2 => "PUT",
        3 => "DELETE",
        4 => "PATCH",
        5 => "HEAD",
        _ => "GET",
    };

    // Create the request builder
    let mut request = ureq::request(method, url_str);

    // Set timeout if specified
    if timeout_ns > 0 {
        let timeout = Duration::from_nanos(timeout_ns as u64);
        request = request.timeout(timeout);
    }

    // Add body if present
    let response = if req_data.body_ptr != 0 && req_data.body_len > 0 {
        let body =
            std::slice::from_raw_parts(req_data.body_ptr as *const u8, req_data.body_len as usize);
        request.send_bytes(body)
    } else {
        request.call()
    };

    match response {
        Ok(resp) => {
            // Read response body
            let status = resp.status();
            let body = match resp.into_string() {
                Ok(s) => s,
                Err(_) => return (0, NetError::HttpInvalidResponse as i64),
            };

            // Allocate response structure
            // Format: status (i64) + body_len (i64) + body_ptr (i64)
            let body_bytes = body.into_bytes();
            let body_len = body_bytes.len();
            let body_box = body_bytes.into_boxed_slice();
            let body_ptr = Box::into_raw(body_box) as *const u8 as i64;

            // Allocate response header: [status, body_len, body_ptr]
            let response_data = Box::new([status as i64, body_len as i64, body_ptr]);
            let response_ptr = Box::into_raw(response_data) as i64;

            (response_ptr, NetError::Success as i64)
        }
        Err(e) => {
            let error_code = match e {
                ureq::Error::Status(code, _) => {
                    // HTTP error status - still return as success with status code
                    // The caller can check the status code
                    if code >= 400 {
                        NetError::HttpError as i64
                    } else {
                        NetError::Success as i64
                    }
                }
                ureq::Error::Transport(transport) => {
                    use ureq::ErrorKind::*;
                    match transport.kind() {
                        InvalidUrl => NetError::HttpInvalidUrl as i64,
                        Dns | ConnectionFailed => NetError::ConnectionRefused as i64,
                        TooManyRedirects => NetError::HttpTooManyRedirects as i64,
                        Io => NetError::Unknown as i64,
                        _ => NetError::HttpError as i64,
                    }
                }
            };
            (0, error_code)
        }
    }
}

/// Free an HTTP response allocated by native_http_send.
#[no_mangle]
pub unsafe extern "C" fn native_http_response_free(response_ptr: i64) {
    if response_ptr == 0 {
        return;
    }

    // Response format: [status, body_len, body_ptr]
    let response_data = Box::from_raw(response_ptr as *mut [i64; 3]);
    let body_ptr = response_data[2];
    let body_len = response_data[1] as usize;

    if body_ptr != 0 && body_len > 0 {
        // Free the body
        let body = std::slice::from_raw_parts_mut(body_ptr as *mut u8, body_len);
        let _ = Box::from_raw(body as *mut [u8]);
    }
}
