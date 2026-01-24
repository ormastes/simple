//! Native networking implementations for the interpreter
//!
//! This module provides implementations for extern functions declared in:
//! - simple/std_lib/src/host/async_nogc_mut/net/tcp.spl
//! - simple/std_lib/src/host/async_nogc_mut/net/udp.spl
//! - simple/std_lib/src/host/async_nogc_mut/net/http.spl

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashMap as StdHashMap;
use std::io::{ErrorKind, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::time::Duration;

// Import shared helper functions from interpreter_native_io
use super::interpreter_native_io::extract_bytes;

//==============================================================================
// Socket Handle Pool
//==============================================================================

use std::sync::atomic::{AtomicI64 as NetAtomicI64, Ordering as NetOrdering};

static NEXT_SOCKET_HANDLE_ID: NetAtomicI64 = NetAtomicI64::new(1000); // Start at 1000 to avoid conflicts

enum SocketHandle {
    TcpListener(TcpListener),
    TcpStream(TcpStream),
    UdpSocket(UdpSocket),
}

thread_local! {
    static SOCKET_HANDLES: RefCell<StdHashMap<i64, SocketHandle>> = RefCell::new(StdHashMap::new());
}

fn allocate_socket(socket: SocketHandle) -> i64 {
    let id = NEXT_SOCKET_HANDLE_ID.fetch_add(1, NetOrdering::SeqCst);
    SOCKET_HANDLES.with(|handles| {
        handles.borrow_mut().insert(id, socket);
    });
    id
}

fn with_tcp_listener<F, R>(id: i64, f: F) -> Result<R, std::io::Error>
where
    F: FnOnce(&TcpListener) -> std::io::Result<R>,
{
    SOCKET_HANDLES.with(|handles| {
        let handles = handles.borrow();
        match handles.get(&id) {
            Some(SocketHandle::TcpListener(listener)) => f(listener),
            Some(_) => Err(std::io::Error::new(ErrorKind::InvalidInput, "not a TCP listener")),
            None => Err(std::io::Error::new(ErrorKind::InvalidInput, "invalid socket handle")),
        }
    })
}

fn with_tcp_stream<F, R>(id: i64, f: F) -> Result<R, std::io::Error>
where
    F: FnOnce(&TcpStream) -> std::io::Result<R>,
{
    SOCKET_HANDLES.with(|handles| {
        let handles = handles.borrow();
        match handles.get(&id) {
            Some(SocketHandle::TcpStream(stream)) => f(stream),
            Some(_) => Err(std::io::Error::new(ErrorKind::InvalidInput, "not a TCP stream")),
            None => Err(std::io::Error::new(ErrorKind::InvalidInput, "invalid socket handle")),
        }
    })
}

fn with_tcp_stream_mut<F, R>(id: i64, f: F) -> Result<R, std::io::Error>
where
    F: FnOnce(&mut TcpStream) -> std::io::Result<R>,
{
    SOCKET_HANDLES.with(|handles| {
        let mut handles = handles.borrow_mut();
        match handles.get_mut(&id) {
            Some(SocketHandle::TcpStream(stream)) => f(stream),
            Some(_) => Err(std::io::Error::new(ErrorKind::InvalidInput, "not a TCP stream")),
            None => Err(std::io::Error::new(ErrorKind::InvalidInput, "invalid socket handle")),
        }
    })
}

fn with_udp_socket<F, R>(id: i64, f: F) -> Result<R, std::io::Error>
where
    F: FnOnce(&UdpSocket) -> std::io::Result<R>,
{
    SOCKET_HANDLES.with(|handles| {
        let handles = handles.borrow();
        match handles.get(&id) {
            Some(SocketHandle::UdpSocket(socket)) => f(socket),
            Some(_) => Err(std::io::Error::new(ErrorKind::InvalidInput, "not a UDP socket")),
            None => Err(std::io::Error::new(ErrorKind::InvalidInput, "invalid socket handle")),
        }
    })
}

fn release_socket(id: i64) -> bool {
    SOCKET_HANDLES.with(|handles| handles.borrow_mut().remove(&id).is_some())
}

//==============================================================================
// Helper Macros for Reducing Duplication
//==============================================================================

/// Wrap operation result with net_ok/net_err
macro_rules! net_result {
    ($expr:expr) => {
        match $expr {
            Ok(v) => Ok(net_ok(v)),
            Err(e) => Ok(net_err(e)),
        }
    };
}

/// Extract handle, call with_tcp_stream, wrap result with net_ok/net_err
macro_rules! with_tcp_stream_op {
    ($args:expr, $idx:expr, $op:expr) => {{
        let handle = extract_handle($args, $idx)?;
        net_result!(with_tcp_stream(handle, $op))
    }};
}

/// Extract handle, call with_tcp_stream_mut, wrap result with net_ok/net_err
macro_rules! with_tcp_stream_mut_op {
    ($args:expr, $idx:expr, $op:expr) => {{
        let handle = extract_handle($args, $idx)?;
        net_result!(with_tcp_stream_mut(handle, $op))
    }};
}

/// Extract handle, call with_udp_socket, wrap result with net_ok/net_err
macro_rules! with_udp_socket_op {
    ($args:expr, $idx:expr, $op:expr) => {{
        let handle = extract_handle($args, $idx)?;
        net_result!(with_udp_socket(handle, $op))
    }};
}

/// Extract handle + timeout, call setter, wrap result (for nil-returning operations)
macro_rules! set_timeout_op {
    ($args:expr, $with_fn:ident, $setter:ident) => {{
        let handle = extract_handle($args, 0)?;
        let timeout = extract_timeout($args, 1);
        net_result!($with_fn(handle, |socket| socket.$setter(timeout).map(|_| Value::Nil)))
    }};
}

/// Extract handle + bool, call setter, wrap result (for nil-returning operations)
macro_rules! set_bool_op {
    ($args:expr, $with_fn:ident, $setter:ident, $default:expr) => {{
        let handle = extract_handle($args, 0)?;
        let flag = $args.get(1).map(|v| v.truthy()).unwrap_or($default);
        net_result!($with_fn(handle, |socket| socket.$setter(flag).map(|_| Value::Nil)))
    }};
}

/// Read into buffer and convert to Value::Array (for operations returning (size, data))
macro_rules! read_to_array {
    ($args:expr, $buf_len_idx:expr, $default_len:expr, $with_fn:ident, $read_fn:ident) => {{
        let handle = extract_handle($args, 0)?;
        let buf_len = $args
            .get($buf_len_idx)
            .and_then(|v| v.as_int().ok())
            .unwrap_or($default_len) as usize;

        let mut buf = vec![0u8; buf_len];
        match $with_fn(handle, |socket| socket.$read_fn(&mut buf)) {
            Ok(n) => {
                buf.truncate(n);
                let arr: Vec<Value> = buf.into_iter().map(|b| Value::Int(b as i64)).collect();
                Ok(net_ok(Value::Array(vec![
                    Value::Int(arr.len() as i64),
                    Value::Array(arr),
                ])))
            }
            Err(e) => Ok(net_err(e)),
        }
    }};
}

/// Read into buffer from address and convert to Value::Array (for operations returning (size, addr, data))
macro_rules! read_from_to_array {
    ($args:expr, $buf_len_idx:expr, $default_len:expr, $read_fn:ident) => {{
        let handle = extract_handle($args, 0)?;
        let buf_len = $args
            .get($buf_len_idx)
            .and_then(|v| v.as_int().ok())
            .unwrap_or($default_len) as usize;

        let mut buf = vec![0u8; buf_len];
        match with_udp_socket(handle, |socket| socket.$read_fn(&mut buf)) {
            Ok((n, addr)) => {
                buf.truncate(n);
                let arr: Vec<Value> = buf.into_iter().map(|b| Value::Int(b as i64)).collect();
                Ok(net_ok(Value::Array(vec![
                    Value::Int(arr.len() as i64),
                    Value::Str(addr.to_string()),
                    Value::Array(arr),
                ])))
            }
            Err(e) => Ok(net_err(e)),
        }
    }};
}

//==============================================================================
// Network Error Helpers
//==============================================================================

fn make_net_error(err: std::io::Error) -> Value {
    let variant = match err.kind() {
        ErrorKind::AddrInUse => "AddrInUse",
        ErrorKind::AddrNotAvailable => "AddrNotAvailable",
        ErrorKind::ConnectionRefused => "ConnectionRefused",
        ErrorKind::ConnectionReset => "ConnectionReset",
        ErrorKind::ConnectionAborted => "ConnectionAborted",
        ErrorKind::NetworkUnreachable => "NetworkUnreachable",
        ErrorKind::HostUnreachable => "HostUnreachable",
        ErrorKind::TimedOut => "TimedOut",
        ErrorKind::WouldBlock => "WouldBlock",
        ErrorKind::PermissionDenied => "PermissionDenied",
        ErrorKind::InvalidInput => "InvalidInput",
        ErrorKind::NotConnected => "NotConnected",
        ErrorKind::AlreadyExists => "AlreadyConnected",
        ErrorKind::BrokenPipe => "BrokenPipe",
        ErrorKind::UnexpectedEof => "UnexpectedEof",
        _ => {
            return Value::Enum {
                enum_name: "IoError".to_string(),
                variant: "Other".to_string(),
                payload: Some(Box::new(Value::Str(err.to_string()))),
            };
        }
    };

    Value::Enum {
        enum_name: "IoError".to_string(),
        variant: variant.to_string(),
        payload: None,
    }
}

fn net_ok(val: Value) -> Value {
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Ok".to_string(),
        payload: Some(Box::new(val)),
    }
}

fn net_err(err: std::io::Error) -> Value {
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: Some(Box::new(make_net_error(err))),
    }
}

fn net_err_msg(msg: &str) -> Value {
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: Some(Box::new(Value::Enum {
            enum_name: "IoError".to_string(),
            variant: "Other".to_string(),
            payload: Some(Box::new(Value::Str(msg.to_string()))),
        })),
    }
}

/// Convert an io::Error to a numeric error code for FFI return values.
/// Returns 0 for success (never called for Ok cases), non-zero for errors.
fn io_error_to_code(err: &std::io::Error) -> i64 {
    match err.kind() {
        ErrorKind::NotFound => 1,
        ErrorKind::PermissionDenied => 2,
        ErrorKind::ConnectionRefused => 3,
        ErrorKind::ConnectionReset => 4,
        ErrorKind::ConnectionAborted => 5,
        ErrorKind::NotConnected => 6,
        ErrorKind::AddrInUse => 7,
        ErrorKind::AddrNotAvailable => 8,
        ErrorKind::NetworkUnreachable => 9,
        ErrorKind::HostUnreachable => 10,
        ErrorKind::BrokenPipe => 11,
        ErrorKind::AlreadyExists => 12,
        ErrorKind::WouldBlock => 13,
        ErrorKind::InvalidInput => 14,
        ErrorKind::InvalidData => 15,
        ErrorKind::TimedOut => 16,
        ErrorKind::WriteZero => 17,
        ErrorKind::Interrupted => 18,
        ErrorKind::UnexpectedEof => 19,
        _ => 255, // Unknown error
    }
}

//==============================================================================
// Value Extraction Helpers for Networking
//==============================================================================

fn extract_socket_addr(args: &[Value], idx: usize) -> Result<SocketAddr, CompileError> {
    let addr_str = match args.get(idx) {
        Some(Value::Str(s)) => s.clone(),
        Some(Value::Object { fields, .. }) => {
            // Handle SocketAddr object
            let ip = fields.get("ip").and_then(|v| match v {
                Value::Str(s) => Some(s.clone()),
                _ => None,
            });
            let port = fields.get("port").and_then(|v| v.as_int().ok());
            match (ip, port) {
                (Some(ip), Some(port)) => format!("{}:{}", ip, port),
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::INVALID_OPERATION)
                        .with_help("SocketAddr object must contain valid ip (string) and port (integer) fields");
                    return Err(CompileError::semantic_with_context(
                        "invalid SocketAddr object".to_string(),
                        ctx,
                    ));
                }
            }
        }
        _ => return Err(crate::error::factory::argument_must_be_socket_address(idx)),
    };

    addr_str
        .parse()
        .map_err(|_| crate::error::factory::invalid_socket_address(&addr_str))
}

fn extract_handle(args: &[Value], idx: usize) -> Result<i64, CompileError> {
    args.get(idx)
        .and_then(|v| v.as_int().ok())
        .ok_or_else(|| crate::error::factory::expected_handle(idx))
}

fn extract_timeout(args: &[Value], idx: usize) -> Option<Duration> {
    args.get(idx)
        .and_then(|v| v.as_int().ok())
        .filter(|&ns| ns > 0)
        .map(|ns| Duration::from_nanos(ns as u64))
}

fn extract_shutdown_how(args: &[Value], idx: usize) -> std::net::Shutdown {
    match args.get(idx) {
        Some(Value::Enum { variant, .. }) => match variant.as_str() {
            "Read" => std::net::Shutdown::Read,
            "Write" => std::net::Shutdown::Write,
            _ => std::net::Shutdown::Both,
        },
        Some(Value::Int(i)) => match i {
            0 => std::net::Shutdown::Read,
            1 => std::net::Shutdown::Write,
            _ => std::net::Shutdown::Both,
        },
        _ => std::net::Shutdown::Both,
    }
}

//==============================================================================
// TCP Functions
//==============================================================================

pub fn native_tcp_bind_interp(args: &[Value]) -> Result<Value, CompileError> {
    let addr = extract_socket_addr(args, 0)?;

    match TcpListener::bind(addr) {
        Ok(listener) => {
            let handle = allocate_socket(SocketHandle::TcpListener(listener));
            // Return tuple (handle, error_code) - 0 means success
            Ok(Value::Tuple(vec![Value::Int(handle), Value::Int(0)]))
        }
        Err(e) => Ok(Value::Tuple(vec![Value::Int(-1), Value::Int(io_error_to_code(&e))])),
    }
}

pub fn native_tcp_accept_interp(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_handle(args, 0)?;

    match with_tcp_listener(handle, |listener| listener.accept()) {
        Ok((stream, peer_addr)) => {
            let stream_handle = allocate_socket(SocketHandle::TcpStream(stream));
            // Return tuple (stream_handle, peer_addr_string)
            Ok(net_ok(Value::Array(vec![
                Value::Int(stream_handle),
                Value::Str(peer_addr.to_string()),
            ])))
        }
        Err(e) => Ok(net_err(e)),
    }
}

pub fn native_tcp_connect_interp(args: &[Value]) -> Result<Value, CompileError> {
    let addr = extract_socket_addr(args, 0)?;

    match TcpStream::connect(addr) {
        Ok(stream) => {
            let local_addr = stream.local_addr().map(|a| a.to_string()).unwrap_or_default();
            let handle = allocate_socket(SocketHandle::TcpStream(stream));
            // Return tuple (handle, local_addr, error_code) - 0 means success
            Ok(Value::Tuple(vec![
                Value::Int(handle),
                Value::Str(local_addr),
                Value::Int(0),
            ]))
        }
        Err(e) => Ok(Value::Tuple(vec![
            Value::Int(-1),
            Value::Str(String::new()),
            Value::Int(io_error_to_code(&e)),
        ])),
    }
}

pub fn native_tcp_connect_timeout_interp(args: &[Value]) -> Result<Value, CompileError> {
    let addr = extract_socket_addr(args, 0)?;
    let timeout = extract_timeout(args, 1).unwrap_or(Duration::from_secs(30));

    net_result!(TcpStream::connect_timeout(&addr, timeout).map(|stream| {
        let local_addr = stream.local_addr().map(|a| a.to_string()).unwrap_or_default();
        let handle = allocate_socket(SocketHandle::TcpStream(stream));
        Value::Array(vec![Value::Int(handle), Value::Str(local_addr)])
    }))
}

pub fn native_tcp_read_interp(args: &[Value]) -> Result<Value, CompileError> {
    read_to_array!(args, 1, 4096, with_tcp_stream_mut, read)
}

pub fn native_tcp_write_interp(args: &[Value]) -> Result<Value, CompileError> {
    let data = extract_bytes(args, 1)?;
    with_tcp_stream_mut_op!(args, 0, |stream| stream.write(&data).map(|n| Value::Int(n as i64)))
}

pub fn native_tcp_flush_interp(args: &[Value]) -> Result<Value, CompileError> {
    with_tcp_stream_mut_op!(args, 0, |stream| stream.flush().map(|_| Value::Nil))
}

pub fn native_tcp_shutdown_interp(args: &[Value]) -> Result<Value, CompileError> {
    let how = extract_shutdown_how(args, 1);
    with_tcp_stream_op!(args, 0, |stream| stream.shutdown(how).map(|_| Value::Nil))
}

pub fn native_tcp_close_interp(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_handle(args, 0)?;

    if release_socket(handle) {
        Ok(Value::Int(0)) // Success
    } else {
        Ok(Value::Int(14)) // InvalidInput error code
    }
}

pub fn native_tcp_set_nodelay_interp(args: &[Value]) -> Result<Value, CompileError> {
    set_bool_op!(args, with_tcp_stream, set_nodelay, true)
}

pub fn native_tcp_set_read_timeout_interp(args: &[Value]) -> Result<Value, CompileError> {
    set_timeout_op!(args, with_tcp_stream, set_read_timeout)
}

pub fn native_tcp_set_write_timeout_interp(args: &[Value]) -> Result<Value, CompileError> {
    set_timeout_op!(args, with_tcp_stream, set_write_timeout)
}

pub fn native_tcp_get_nodelay_interp(args: &[Value]) -> Result<Value, CompileError> {
    with_tcp_stream_op!(args, 0, |stream| stream.nodelay().map(Value::Bool))
}

pub fn native_tcp_peek_interp(args: &[Value]) -> Result<Value, CompileError> {
    read_to_array!(args, 1, 4096, with_tcp_stream, peek)
}

//==============================================================================
// UDP Functions
//==============================================================================

pub fn native_udp_bind_interp(args: &[Value]) -> Result<Value, CompileError> {
    let addr = extract_socket_addr(args, 0)?;

    match UdpSocket::bind(addr) {
        Ok(socket) => {
            let handle = allocate_socket(SocketHandle::UdpSocket(socket));
            // Return tuple (handle, error_code) - 0 means success
            Ok(Value::Tuple(vec![Value::Int(handle), Value::Int(0)]))
        }
        Err(e) => Ok(Value::Tuple(vec![Value::Int(-1), Value::Int(io_error_to_code(&e))])),
    }
}

pub fn native_udp_connect_interp(args: &[Value]) -> Result<Value, CompileError> {
    let addr = extract_socket_addr(args, 1)?;
    with_udp_socket_op!(args, 0, |socket| socket.connect(addr).map(|_| Value::Nil))
}

pub fn native_udp_recv_from_interp(args: &[Value]) -> Result<Value, CompileError> {
    read_from_to_array!(args, 1, 65535, recv_from)
}

pub fn native_udp_recv_interp(args: &[Value]) -> Result<Value, CompileError> {
    read_to_array!(args, 1, 65535, with_udp_socket, recv)
}

pub fn native_udp_send_to_interp(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_handle(args, 0)?;
    let data = extract_bytes(args, 1)?;
    // args[2] is len, which we skip since we get length from the array
    let addr = extract_socket_addr(args, 3)?;

    match with_udp_socket(handle, |socket| socket.send_to(&data, addr)) {
        // Return tuple (bytes_sent, error_code) - error_code 0 means success
        Ok(n) => Ok(Value::Tuple(vec![Value::Int(n as i64), Value::Int(0)])),
        Err(e) => Ok(Value::Tuple(vec![Value::Int(0), Value::Int(io_error_to_code(&e))])),
    }
}

pub fn native_udp_send_interp(args: &[Value]) -> Result<Value, CompileError> {
    let data = extract_bytes(args, 1)?;
    with_udp_socket_op!(args, 0, |socket| socket.send(&data).map(|n| Value::Int(n as i64)))
}

pub fn native_udp_set_broadcast_interp(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_handle(args, 0)?;
    let broadcast = args.get(1).map(|v| v.truthy()).unwrap_or(true);

    match with_udp_socket(handle, |socket| socket.set_broadcast(broadcast)) {
        Ok(()) => Ok(Value::Int(0)), // Success
        Err(e) => Ok(Value::Int(io_error_to_code(&e))),
    }
}

pub fn native_udp_set_ttl_interp(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_handle(args, 0)?;
    let ttl = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(64) as u32;

    match with_udp_socket(handle, |socket| socket.set_ttl(ttl)) {
        Ok(()) => Ok(Value::Int(0)), // Success
        Err(e) => Ok(Value::Int(io_error_to_code(&e))),
    }
}

pub fn native_udp_close_interp(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_handle(args, 0)?;

    if release_socket(handle) {
        Ok(Value::Int(0)) // Success
    } else {
        Ok(Value::Int(14)) // InvalidInput error code
    }
}

pub fn native_udp_peek_from_interp(args: &[Value]) -> Result<Value, CompileError> {
    read_from_to_array!(args, 1, 65535, peek_from)
}

pub fn native_udp_peek_interp(args: &[Value]) -> Result<Value, CompileError> {
    read_to_array!(args, 1, 65535, with_udp_socket, peek)
}

pub fn native_udp_peer_addr_interp(args: &[Value]) -> Result<Value, CompileError> {
    with_udp_socket_op!(args, 0, |socket| socket
        .peer_addr()
        .map(|addr| Value::Str(addr.to_string())))
}

pub fn native_udp_set_multicast_loop_interp(args: &[Value]) -> Result<Value, CompileError> {
    let on = args.get(1).map(|v| v.truthy()).unwrap_or(true);
    with_udp_socket_op!(args, 0, |socket| {
        socket
            .set_multicast_loop_v4(on)
            .or_else(|_| socket.set_multicast_loop_v6(on))
            .map(|_| Value::Nil)
    })
}

pub fn native_udp_set_multicast_ttl_interp(args: &[Value]) -> Result<Value, CompileError> {
    let ttl = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(1) as u32;
    with_udp_socket_op!(args, 0, |socket| socket.set_multicast_ttl_v4(ttl).map(|_| Value::Nil))
}

pub fn native_udp_set_read_timeout_interp(args: &[Value]) -> Result<Value, CompileError> {
    set_timeout_op!(args, with_udp_socket, set_read_timeout)
}

pub fn native_udp_set_write_timeout_interp(args: &[Value]) -> Result<Value, CompileError> {
    set_timeout_op!(args, with_udp_socket, set_write_timeout)
}

pub fn native_udp_get_broadcast_interp(args: &[Value]) -> Result<Value, CompileError> {
    with_udp_socket_op!(args, 0, |socket| socket.broadcast().map(Value::Bool))
}

pub fn native_udp_get_ttl_interp(args: &[Value]) -> Result<Value, CompileError> {
    with_udp_socket_op!(args, 0, |socket| socket.ttl().map(|ttl| Value::Int(ttl as i64)))
}

pub fn native_udp_join_multicast_v4_interp(args: &[Value]) -> Result<Value, CompileError> {
    let multiaddr = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(0) as u32;
    let interface = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0) as u32;
    let multi = std::net::Ipv4Addr::from(multiaddr.to_be_bytes());
    let iface = std::net::Ipv4Addr::from(interface.to_be_bytes());

    with_udp_socket_op!(args, 0, |socket| socket
        .join_multicast_v4(&multi, &iface)
        .map(|_| Value::Nil))
}

pub fn native_udp_leave_multicast_v4_interp(args: &[Value]) -> Result<Value, CompileError> {
    let multiaddr = args.get(1).and_then(|v| v.as_int().ok()).unwrap_or(0) as u32;
    let interface = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0) as u32;
    let multi = std::net::Ipv4Addr::from(multiaddr.to_be_bytes());
    let iface = std::net::Ipv4Addr::from(interface.to_be_bytes());

    with_udp_socket_op!(args, 0, |socket| socket
        .leave_multicast_v4(&multi, &iface)
        .map(|_| Value::Nil))
}

pub fn native_udp_join_multicast_v6_interp(args: &[Value]) -> Result<Value, CompileError> {
    let interface = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0) as u32;
    let multi = match args.get(1) {
        Some(Value::Array(arr)) if arr.len() >= 16 => {
            let mut bytes = [0u8; 16];
            for (i, v) in arr.iter().take(16).enumerate() {
                bytes[i] = v.as_int().unwrap_or(0) as u8;
            }
            std::net::Ipv6Addr::from(bytes)
        }
        _ => std::net::Ipv6Addr::UNSPECIFIED,
    };

    with_udp_socket_op!(args, 0, |socket| socket
        .join_multicast_v6(&multi, interface)
        .map(|_| Value::Nil))
}

pub fn native_udp_leave_multicast_v6_interp(args: &[Value]) -> Result<Value, CompileError> {
    let interface = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0) as u32;
    let multi = match args.get(1) {
        Some(Value::Array(arr)) if arr.len() >= 16 => {
            let mut bytes = [0u8; 16];
            for (i, v) in arr.iter().take(16).enumerate() {
                bytes[i] = v.as_int().unwrap_or(0) as u8;
            }
            std::net::Ipv6Addr::from(bytes)
        }
        _ => std::net::Ipv6Addr::UNSPECIFIED,
    };

    with_udp_socket_op!(args, 0, |socket| socket
        .leave_multicast_v6(&multi, interface)
        .map(|_| Value::Nil))
}

//==============================================================================
// HTTP Functions
//==============================================================================

pub fn native_http_send_interp(args: &[Value]) -> Result<Value, CompileError> {
    // Extract request details
    let method = match args.get(0) {
        Some(Value::Enum { variant, .. }) => variant.clone(),
        Some(Value::Str(s)) => s.clone(),
        _ => "GET".to_string(),
    };

    let url = match args.get(1) {
        Some(Value::Str(s)) => s.clone(),
        Some(Value::Object { fields, .. }) => {
            // Handle HttpUrl object
            fields
                .get("url")
                .and_then(|v| match v {
                    Value::Str(s) => Some(s.clone()),
                    _ => None,
                })
                .unwrap_or_default()
        }
        _ => return Ok(net_err_msg("invalid URL")),
    };

    let body = match args.get(2) {
        Some(Value::Array(arr)) => Some(
            arr.iter()
                .filter_map(|v| v.as_int().ok().map(|i| i as u8))
                .collect::<Vec<_>>(),
        ),
        Some(Value::Str(s)) => Some(s.as_bytes().to_vec()),
        _ => None,
    };

    let timeout = extract_timeout(args, 3);

    // Build and send request using ureq
    let method_str = method.to_uppercase();
    let mut request = ureq::request(&method_str, &url);

    if let Some(t) = timeout {
        request = request.timeout(t);
    }

    let response = if let Some(body_data) = body {
        request.send_bytes(&body_data)
    } else {
        request.call()
    };

    match response {
        Ok(resp) => {
            let status = resp.status();
            let body_str = resp.into_string().unwrap_or_default();

            // Return response object
            let mut fields = HashMap::new();
            fields.insert("status".to_string(), Value::Int(status as i64));
            fields.insert("body".to_string(), Value::Str(body_str));

            Ok(net_ok(Value::Object {
                class: "HttpResponse".to_string(),
                fields,
            }))
        }
        Err(e) => {
            let error_msg = match e {
                ureq::Error::Status(code, _) => format!("HTTP status {}", code),
                ureq::Error::Transport(t) => format!("Transport error: {:?}", t.kind()),
            };
            Ok(net_err_msg(&error_msg))
        }
    }
}

/// Clear all socket handles and network state.
///
/// This should be called between test runs to prevent memory leaks
/// from unclosed sockets.
pub fn clear_net_state() {
    SOCKET_HANDLES.with(|handles| {
        // Drop all socket handles (this closes them)
        handles.borrow_mut().clear();
    });
}
