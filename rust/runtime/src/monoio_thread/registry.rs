// Stream Registry

use monoio::net::udp::UdpSocket;
use monoio::net::{TcpListener, TcpStream};
use std::collections::HashMap;

/// Stores active TCP/UDP connections
pub(crate) struct StreamRegistry {
    next_id: i64,
    tcp_listeners: HashMap<i64, TcpListener>,
    tcp_streams: HashMap<i64, TcpStream>,
    udp_sockets: HashMap<i64, UdpSocket>,
}

impl StreamRegistry {
    pub fn new() -> Self {
        Self {
            next_id: 1,
            tcp_listeners: HashMap::new(),
            tcp_streams: HashMap::new(),
            udp_sockets: HashMap::new(),
        }
    }

    fn alloc_id(&mut self) -> i64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    pub fn add_tcp_listener(&mut self, listener: TcpListener) -> i64 {
        let id = self.alloc_id();
        self.tcp_listeners.insert(id, listener);
        id
    }

    pub fn add_tcp_stream(&mut self, stream: TcpStream) -> i64 {
        let id = self.alloc_id();
        self.tcp_streams.insert(id, stream);
        id
    }

    pub fn add_udp_socket(&mut self, socket: UdpSocket) -> i64 {
        let id = self.alloc_id();
        self.udp_sockets.insert(id, socket);
        id
    }

    pub fn get_tcp_listener(&mut self, id: i64) -> Option<&mut TcpListener> {
        self.tcp_listeners.get_mut(&id)
    }

    pub fn get_tcp_stream(&mut self, id: i64) -> Option<&mut TcpStream> {
        self.tcp_streams.get_mut(&id)
    }

    pub fn get_udp_socket(&mut self, id: i64) -> Option<&mut UdpSocket> {
        self.udp_sockets.get_mut(&id)
    }

    pub fn remove_tcp_listener(&mut self, id: i64) -> bool {
        self.tcp_listeners.remove(&id).is_some()
    }

    pub fn remove_tcp_stream(&mut self, id: i64) -> bool {
        self.tcp_streams.remove(&id).is_some()
    }

    pub fn remove_udp_socket(&mut self, id: i64) -> bool {
        self.udp_sockets.remove(&id).is_some()
    }
}
