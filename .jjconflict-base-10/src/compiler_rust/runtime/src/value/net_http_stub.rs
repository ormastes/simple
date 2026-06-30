// HTTP stubs used when runtime-http is disabled.

#[no_mangle]
pub unsafe extern "C" fn native_http_send(_request_ptr: i64, _timeout_ns: i64) -> (i64, i64) {
    (0, NetError::HttpError as i64)
}

#[no_mangle]
pub unsafe extern "C" fn native_http_response_free(_response_ptr: i64) {}
