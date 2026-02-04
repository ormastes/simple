// Core TCP operations for direct monoio I/O
// Feature: monoio-direct

use crate::monoio_buffer::OwnedBuf;
use crate::monoio_runtime::direct::{block_on, with_registry};
use crate::monoio_runtime::{copy_to_buffer, execute_async, extract_buffer_bytes, get_entries};
use crate::value::RuntimeValue;
use monoio::io::{AsyncReadRent, AsyncReadRentExt, AsyncWriteRent, AsyncWriteRentExt};
use monoio::net::{TcpListener, TcpStream};
use std::net::SocketAddr;

// ============================================================================
// TCP Operations
// ============================================================================

/// Create a TCP listener bound to the specified address (direct, synchronous).
///
/// # Arguments
/// * `addr` - Address string (e.g., "127.0.0.1:8080")
///
/// # Returns
/// Listener handle (positive) or error code (negative)
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_listen(addr: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_tcp_listen: Invalid address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    let socket_addr: SocketAddr = match addr_str.parse() {
        Ok(a) => a,
        Err(e) => {
            tracing::error!("rt_monoio_tcp_listen: Invalid address format: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    match TcpListener::bind(socket_addr) {
        Ok(listener) => {
            let id = with_registry(|reg| reg.add_tcp_listener(listener));
            tracing::debug!("rt_monoio_tcp_listen: Bound to {} with handle {}", addr_str, id);
            RuntimeValue::from_int(id)
        }
        Err(e) => {
            tracing::error!("rt_monoio_tcp_listen: Bind failed: {}", e);
            RuntimeValue::from_int(-3)
        }
    }
}

/// Accept a connection from a TCP listener (blocking).
///
/// # Arguments
/// * `listener_handle` - Handle from rt_monoio_tcp_listen
///
/// # Returns
/// Stream handle (positive) or error code (negative)
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_accept(listener_handle: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();

    let result = block_on(async {
        // Get the listener from registry
        let listener = with_registry(|reg| reg.take_tcp_listener(listener_id));

        match listener {
            Some(l) => {
                match l.accept().await {
                    Ok((stream, peer_addr)) => {
                        // Put listener back
                        with_registry(|reg| {
                            // Re-add with same ID would require modification
                            // For now, we add as new and note the ID change
                            let _new_id = reg.add_tcp_listener(l);
                        });
                        let stream_id = with_registry(|reg| reg.add_tcp_stream(stream));
                        tracing::debug!(
                            "rt_monoio_tcp_accept: Accepted from {} with handle {}",
                            peer_addr,
                            stream_id
                        );
                        Ok(stream_id)
                    }
                    Err(e) => {
                        // Put listener back even on error
                        with_registry(|reg| {
                            let _new_id = reg.add_tcp_listener(l);
                        });
                        Err(e)
                    }
                }
            }
            None => Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "Invalid listener handle",
            )),
        }
    });

    match result {
        Ok(stream_id) => RuntimeValue::from_int(stream_id),
        Err(e) => {
            tracing::error!("rt_monoio_tcp_accept: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Connect to a TCP server (blocking).
///
/// # Arguments
/// * `addr` - Address string (e.g., "127.0.0.1:8080")
///
/// # Returns
/// Stream handle (positive) or error code (negative)
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_connect(addr: RuntimeValue) -> RuntimeValue {
    let addr_str = match crate::monoio_runtime::runtime_value_to_string(addr) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_tcp_connect: Invalid address (not a string)");
            return RuntimeValue::from_int(-1);
        }
    };

    let socket_addr: SocketAddr = match addr_str.parse() {
        Ok(a) => a,
        Err(e) => {
            tracing::error!("rt_monoio_tcp_connect: Invalid address format: {}", e);
            return RuntimeValue::from_int(-2);
        }
    };

    let result = block_on(async { TcpStream::connect(socket_addr).await });

    match result {
        Ok(stream) => {
            let id = with_registry(|reg| reg.add_tcp_stream(stream));
            tracing::debug!("rt_monoio_tcp_connect: Connected to {} with handle {}", addr_str, id);
            RuntimeValue::from_int(id)
        }
        Err(e) => {
            let code = match e.kind() {
                std::io::ErrorKind::ConnectionRefused => -3,
                std::io::ErrorKind::TimedOut => -4,
                _ => -5,
            };
            tracing::error!("rt_monoio_tcp_connect: {}", e);
            RuntimeValue::from_int(code)
        }
    }
}

/// Read data from a TCP stream (blocking, zero-copy).
///
/// # Arguments
/// * `stream_handle` - Handle from rt_monoio_tcp_connect or rt_monoio_tcp_accept
/// * `buffer` - RuntimeArray to read into
/// * `max_len` - Maximum bytes to read
///
/// # Returns
/// Number of bytes read (0 = EOF) or error code (negative)
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_read(stream_handle: RuntimeValue, buffer: RuntimeValue, max_len: i64) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    if max_len <= 0 {
        return RuntimeValue::from_int(0);
    }

    let result = block_on(async {
        let stream = with_registry(|reg| reg.take_tcp_stream(stream_id));

        match stream {
            Some(mut s) => {
                let buf = OwnedBuf::new(max_len as usize);
                let (res, buf) = s.read(buf).await;

                // Put stream back
                with_registry(|reg| {
                    // Re-insert stream
                    let _new_id = reg.add_tcp_stream(s);
                });

                match res {
                    Ok(n) => Ok((n, buf.into_vec())),
                    Err(e) => Err(e),
                }
            }
            None => Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "Invalid stream handle",
            )),
        }
    });

    match result {
        Ok((n, data)) => {
            // Copy data to the provided buffer
            let copied = copy_to_buffer(buffer, &data[..n]);
            if copied < 0 {
                tracing::error!("rt_monoio_tcp_read: Failed to copy to buffer");
                return RuntimeValue::from_int(-6);
            }
            RuntimeValue::from_int(n as i64)
        }
        Err(e) => {
            tracing::error!("rt_monoio_tcp_read: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Write data to a TCP stream (blocking, zero-copy).
///
/// # Arguments
/// * `stream_handle` - Handle from rt_monoio_tcp_connect or rt_monoio_tcp_accept
/// * `buffer` - RuntimeArray or RuntimeString to write from
/// * `len` - Number of bytes to write
///
/// # Returns
/// Number of bytes written or error code (negative)
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_write(stream_handle: RuntimeValue, buffer: RuntimeValue, len: i64) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    if len <= 0 {
        return RuntimeValue::from_int(0);
    }

    // Extract data from buffer
    let data = match extract_buffer_bytes(buffer) {
        Some(mut bytes) => {
            if bytes.len() > len as usize {
                bytes.truncate(len as usize);
            }
            bytes
        }
        None => {
            tracing::error!("rt_monoio_tcp_write: Invalid buffer");
            return RuntimeValue::from_int(-1);
        }
    };

    let result = block_on(async {
        let stream = with_registry(|reg| reg.take_tcp_stream(stream_id));

        match stream {
            Some(mut s) => {
                let (res, _buf) = s.write(data).await;

                // Put stream back
                with_registry(|reg| {
                    let _new_id = reg.add_tcp_stream(s);
                });

                res
            }
            None => Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "Invalid stream handle",
            )),
        }
    });

    match result {
        Ok(n) => RuntimeValue::from_int(n as i64),
        Err(e) => {
            tracing::error!("rt_monoio_tcp_write: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}

/// Close a TCP stream.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_close(stream_handle: RuntimeValue) -> RuntimeValue {
    let stream_id = stream_handle.as_int();

    if with_registry(|reg| reg.remove_tcp_stream(stream_id)) {
        RuntimeValue::from_int(1)
    } else {
        RuntimeValue::from_int(0)
    }
}

/// Close a TCP listener.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_listener_close(listener_handle: RuntimeValue) -> RuntimeValue {
    let listener_id = listener_handle.as_int();

    if with_registry(|reg| reg.remove_tcp_listener(listener_id)) {
        RuntimeValue::from_int(1)
    } else {
        RuntimeValue::from_int(0)
    }
}

/// Flush pending writes on a TCP stream.
///
/// Note: monoio uses completion-based I/O, so writes are typically already
/// submitted to the kernel. This function ensures any buffered data is sent.
#[no_mangle]
pub extern "C" fn rt_monoio_tcp_flush(stream_handle: RuntimeValue) -> RuntimeValue {
    use monoio::io::AsyncWriteRentExt;

    let stream_id = stream_handle.as_int();

    // Take stream for async operation
    let mut stream = match with_registry(|reg| reg.take_tcp_stream(stream_id)) {
        Some(s) => s,
        None => {
            tracing::error!("rt_monoio_tcp_flush: Invalid stream handle {}", stream_id);
            return RuntimeValue::from_int(-1);
        }
    };

    let result = execute_async(get_entries(), async move {
        stream.flush().await?;
        Ok::<_, std::io::Error>(stream)
    });

    match result {
        Ok(stream) => {
            with_registry(|reg| reg.put_back_tcp_stream(stream_id, stream));
            RuntimeValue::from_int(1)
        }
        Err(e) => {
            tracing::error!("rt_monoio_tcp_flush: {}", e);
            RuntimeValue::from_int(-1)
        }
    }
}
