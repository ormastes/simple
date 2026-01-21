// Runtime execution logic for async operations
// Handles the actual async I/O execution via monoio runtime.

#![cfg(feature = "monoio-direct")]

use crate::monoio_buffer::OwnedBuf;
use monoio::io::{AsyncReadRent, AsyncWriteRent, AsyncWriteRentExt};
use monoio::net::TcpStream;
use std::cell::RefCell;
use std::collections::HashMap;
use std::net::SocketAddr;
use std::rc::Rc;

use super::types::{OpResult, OpType};

/// Execute a single operation (async implementation)
pub async fn execute_operation(
    op_type: OpType,
    handle_id: i64,
    addr: Option<String>,
    data: Option<Vec<u8>>,
    max_len: usize,
    listeners: &Rc<RefCell<HashMap<i64, monoio::net::TcpListener>>>,
    streams: &Rc<RefCell<HashMap<i64, TcpStream>>>,
    sockets: &Rc<RefCell<HashMap<i64, monoio::net::udp::UdpSocket>>>,
    new_streams: &Rc<RefCell<Vec<(u64, TcpStream)>>>,
    op_id: u64,
) -> Result<OpResult, String> {
    match op_type {
        OpType::TcpAccept => {
            let listener = listeners.borrow_mut().remove(&handle_id);
            match listener {
                Some(l) => {
                    let res = l.accept().await;
                    listeners.borrow_mut().insert(handle_id, l);
                    match res {
                        Ok((stream, _addr)) => {
                            new_streams.borrow_mut().push((op_id, stream));
                            Ok(OpResult::Handle(0)) // Placeholder, will update
                        }
                        Err(e) => Err(format!("Accept failed: {}", e)),
                    }
                }
                None => Err("Listener not available".to_string()),
            }
        }
        OpType::TcpConnect => {
            let addr_str = addr.unwrap_or_default();
            match addr_str.parse::<SocketAddr>() {
                Ok(socket_addr) => match TcpStream::connect(socket_addr).await {
                    Ok(stream) => {
                        new_streams.borrow_mut().push((op_id, stream));
                        Ok(OpResult::Handle(0)) // Placeholder
                    }
                    Err(e) => Err(format!("Connect failed: {}", e)),
                },
                Err(e) => Err(format!("Invalid address: {}", e)),
            }
        }
        OpType::TcpRead => {
            let stream = streams.borrow_mut().remove(&handle_id);
            match stream {
                Some(mut s) => {
                    let buf = OwnedBuf::new(max_len);
                    let (res, buf) = s.read(buf).await;
                    streams.borrow_mut().insert(handle_id, s);
                    match res {
                        Ok(n) => Ok(OpResult::Data(buf.into_vec()[..n].to_vec())),
                        Err(e) => Err(format!("Read failed: {}", e)),
                    }
                }
                None => Err("Stream not available".to_string()),
            }
        }
        OpType::TcpWrite => {
            let stream = streams.borrow_mut().remove(&handle_id);
            let write_data = data.unwrap_or_default();
            match stream {
                Some(mut s) => {
                    let (res, _) = s.write(write_data).await;
                    streams.borrow_mut().insert(handle_id, s);
                    match res {
                        Ok(n) => Ok(OpResult::Bytes(n)),
                        Err(e) => Err(format!("Write failed: {}", e)),
                    }
                }
                None => Err("Stream not available".to_string()),
            }
        }
        OpType::UdpRecvFrom => {
            let socket = sockets.borrow_mut().remove(&handle_id);
            match socket {
                Some(s) => {
                    let buf = OwnedBuf::new(max_len);
                    let (res, buf) = s.recv_from(buf).await;
                    sockets.borrow_mut().insert(handle_id, s);
                    match res {
                        Ok((n, addr)) => Ok(OpResult::DataFrom(buf.into_vec()[..n].to_vec(), addr)),
                        Err(e) => Err(format!("RecvFrom failed: {}", e)),
                    }
                }
                None => Err("Socket not available".to_string()),
            }
        }
        OpType::UdpSendTo => {
            let socket = sockets.borrow_mut().remove(&handle_id);
            let send_data = data.unwrap_or_default();
            let addr_str = addr.unwrap_or_default();
            match socket {
                Some(s) => match addr_str.parse::<SocketAddr>() {
                    Ok(socket_addr) => {
                        let (res, _) = s.send_to(send_data, socket_addr).await;
                        sockets.borrow_mut().insert(handle_id, s);
                        match res {
                            Ok(n) => Ok(OpResult::Bytes(n)),
                            Err(e) => Err(format!("SendTo failed: {}", e)),
                        }
                    }
                    Err(e) => {
                        sockets.borrow_mut().insert(handle_id, s);
                        Err(format!("Invalid address: {}", e))
                    }
                },
                None => Err("Socket not available".to_string()),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_compiles() {
        // Basic compilation test
        assert!(true);
    }
}
