//! Networking stack stubs. SimpleOS has no kernel networking yet.

use crate::fmt;
use crate::io::{self, IoSlice, IoSliceMut};
use crate::net::{Shutdown, SocketAddr};
use crate::time::Duration;

pub struct TcpStream(!);
pub struct TcpListener(!);
pub struct UdpSocket(!);
pub struct LookupHost(!);

fn unsup<T>() -> io::Result<T> {
    Err(io::Error::from(io::ErrorKind::Unsupported))
}

#[rustfmt::skip]
impl Iterator for LookupHost {
    type Item = SocketAddr;
    fn next(&mut self) -> Option<SocketAddr> { self.0 }
}
#[rustfmt::skip]
impl LookupHost {
    pub fn port(&self) -> u16 { self.0 }
}

impl<'a> TryFrom<(&'a str, u16)> for LookupHost {
    type Error = io::Error;
    fn try_from(_v: (&'a str, u16)) -> io::Result<LookupHost> { unsup() }
}
impl<'a> TryFrom<&'a str> for LookupHost {
    type Error = io::Error;
    fn try_from(_v: &'a str) -> io::Result<LookupHost> { unsup() }
}

macro_rules! stream_like {
    ($t:ident) => {
        #[rustfmt::skip]
        impl $t {
            pub fn connect(_a: io::Result<&SocketAddr>) -> io::Result<$t> { unsup() }
            pub fn peer_addr(&self) -> io::Result<SocketAddr>            { self.0 }
            pub fn socket_addr(&self) -> io::Result<SocketAddr>          { self.0 }
            pub fn shutdown(&self, _h: Shutdown) -> io::Result<()>       { self.0 }
            pub fn duplicate(&self) -> io::Result<$t>                    { self.0 }
            pub fn set_read_timeout(&self, _d: Option<Duration>) -> io::Result<()> { self.0 }
            pub fn set_write_timeout(&self, _d: Option<Duration>) -> io::Result<()> { self.0 }
            pub fn read_timeout(&self) -> io::Result<Option<Duration>>   { self.0 }
            pub fn write_timeout(&self) -> io::Result<Option<Duration>>  { self.0 }
            pub fn set_nonblocking(&self, _n: bool) -> io::Result<()>    { self.0 }
            pub fn read(&self, _b: &mut [u8]) -> io::Result<usize>       { self.0 }
            pub fn read_vectored(&self, _b: &mut [IoSliceMut<'_>]) -> io::Result<usize> { self.0 }
            pub fn write(&self, _b: &[u8]) -> io::Result<usize>          { self.0 }
            pub fn write_vectored(&self, _b: &[IoSlice<'_>]) -> io::Result<usize> { self.0 }
            pub fn is_read_vectored(&self) -> bool                       { self.0 }
            pub fn is_write_vectored(&self) -> bool                      { self.0 }
            pub fn take_error(&self) -> io::Result<Option<io::Error>>    { self.0 }
        }
        #[rustfmt::skip]
        impl fmt::Debug for $t {
            fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result { self.0 }
        }
    };
}

stream_like!(TcpStream);

#[rustfmt::skip]
impl TcpListener {
    pub fn bind(_a: io::Result<&SocketAddr>) -> io::Result<TcpListener> { unsup() }
    pub fn socket_addr(&self) -> io::Result<SocketAddr>                 { self.0 }
    pub fn accept(&self) -> io::Result<(TcpStream, SocketAddr)>         { self.0 }
    pub fn duplicate(&self) -> io::Result<TcpListener>                  { self.0 }
    pub fn set_ttl(&self, _t: u32) -> io::Result<()>                    { self.0 }
    pub fn ttl(&self) -> io::Result<u32>                                { self.0 }
    pub fn set_only_v6(&self, _v: bool) -> io::Result<()>               { self.0 }
    pub fn only_v6(&self) -> io::Result<bool>                           { self.0 }
    pub fn take_error(&self) -> io::Result<Option<io::Error>>           { self.0 }
    pub fn set_nonblocking(&self, _n: bool) -> io::Result<()>           { self.0 }
}
#[rustfmt::skip]
impl fmt::Debug for TcpListener {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result { self.0 }
}

#[rustfmt::skip]
impl UdpSocket {
    pub fn bind(_a: io::Result<&SocketAddr>) -> io::Result<UdpSocket> { unsup() }
    pub fn peer_addr(&self) -> io::Result<SocketAddr>                 { self.0 }
    pub fn socket_addr(&self) -> io::Result<SocketAddr>               { self.0 }
    pub fn recv_from(&self, _b: &mut [u8]) -> io::Result<(usize, SocketAddr)> { self.0 }
    pub fn peek_from(&self, _b: &mut [u8]) -> io::Result<(usize, SocketAddr)> { self.0 }
    pub fn send_to(&self, _b: &[u8], _a: &SocketAddr) -> io::Result<usize> { self.0 }
    pub fn duplicate(&self) -> io::Result<UdpSocket>                  { self.0 }
    pub fn set_nonblocking(&self, _n: bool) -> io::Result<()>         { self.0 }
    pub fn take_error(&self) -> io::Result<Option<io::Error>>         { self.0 }
    pub fn recv(&self, _b: &mut [u8]) -> io::Result<usize>            { self.0 }
    pub fn send(&self, _b: &[u8]) -> io::Result<usize>                { self.0 }
    pub fn connect(&self, _a: io::Result<&SocketAddr>) -> io::Result<()> { self.0 }
}
#[rustfmt::skip]
impl fmt::Debug for UdpSocket {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result { self.0 }
}
