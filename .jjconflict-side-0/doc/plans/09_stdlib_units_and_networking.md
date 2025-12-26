# Plan: Standard Library Units and Networking

## Overview

This plan defines the standard library implementation with:
1. **Default variant**: `async` + `nogc` as the common default
2. **Unit postfixes for all types**: File paths, network addresses, URLs, etc.
3. **String warning in public APIs**: Enforce semantic types even for string-based values
4. **Comprehensive networking**: TCP, UDP, HTTP, FTP with proper unit types

---

## 1. Default Variant: async_nogc

### 1.1 Rationale

The default variant should be `async_nogc` because:
- **async**: Modern applications are I/O bound; async enables efficient concurrency
- **nogc**: Predictable performance, no GC pauses, suitable for servers/embedded
- Libraries written for `nogc` can be used in `gc` contexts (not vice versa)

### 1.2 Profile Configuration

```toml
# simple.toml - default profile
[profiles.default]
attributes = ["platform_host", "async", "no_gc", "strong"]
imports = ["std.*"]

[profiles.server]
attributes = ["platform_host", "async", "no_gc", "strong"]
imports = ["std.*", "std.net.*"]

[profiles.app]
attributes = ["platform_host", "async", "gc", "strong"]
imports = ["std.*"]
```

### 1.3 Directory Structure

```
lib/std/
├── __init__.spl              # #[deny(primitive_api)] #[deny(bare_string)]
├── core/                     # #[variant(any)] - pure, no allocation
│   ├── __init__.spl
│   ├── units.spl             # Unit type infrastructure
│   ├── option.spl
│   ├── result.spl
│   └── traits.spl
├── core_nogc/                # #[no_gc] #[variant(any)]
│   ├── __init__.spl
│   ├── arena.spl
│   └── fixed_vec.spl
├── host/
│   ├── async_nogc/           # DEFAULT - async + no_gc
│   │   ├── __init__.spl
│   │   ├── io/
│   │   │   ├── fs.spl
│   │   │   └── buf.spl
│   │   └── net/
│   │       ├── tcp.spl
│   │       ├── udp.spl
│   │       ├── http.spl
│   │       └── ftp.spl
│   ├── async_gc/             # async + gc (for convenience)
│   └── sync_nogc/            # blocking + no_gc
└── units/                    # All unit type definitions
    ├── __init__.spl
    ├── ids.spl
    ├── file.spl              # FilePath, FileName, FileExt
    ├── net.spl               # IpAddr, Port, MacAddr
    ├── url.spl               # Url, HttpUrl, FtpUrl
    └── physical/
```

---

## 2. String Warning in Public APIs

### 2.1 New Lint: `bare_string`

**Problem**: Even `str`/`String` is too generic for public APIs. A file path is not just a string.

**Solution**: Add `bare_string` lint alongside `primitive_api`:

```simple
# WARNING: Bare string in public function
pub fn read_file(path: str) -> Result[Bytes, IoError]:  # Warning!
    ...

# OK: Semantic type (no warning)
pub fn read_file(path: FilePath) -> Result[Bytes, IoError]:
    ...
```

### 2.2 Lint Levels

```simple
# std/__init__.spl
#[deny(primitive_api)]
#[deny(bare_string)]        # NEW: all string types must be semantic
mod std
```

### 2.3 Exemptions

Some cases legitimately need raw strings:
- `fmt` module (formatting arbitrary values)
- `log` module (logging messages)
- Low-level parsing utilities

```simple
#[allow(bare_string)]
pub fn format(template: str, args: ...) -> String:
    ...
```

### 2.4 Configuration

```toml
# simple.toml
[lint]
primitive_api = "deny"
bare_string = "deny"        # NEW
bare_bool = "deny"
```

---

## 3. File System Units

### 3.1 File Path Unit: `_file`

Supports cross-platform paths including Windows drive letters (mingw-style):

```simple
# std/units/file.spl

# FilePath - platform-aware file path
unit FilePath: str as file

# FilePath components
unit FileName: str as filename
unit FileExt: str as ext
unit DirPath: str as dir

# Drive letter for Windows (optional)
unit DriveLetter: str as drive   # "C", "D", etc.

# Usage examples
let path = "/home/user/data.txt"_file
let win_path = "C:/Users/data.txt"_file  # mingw-style with drive
let name = "config"_filename
let ext = "json"_ext
```

### 3.2 FilePath API

```simple
# std/units/file.spl

impl FilePath:
    # Construction
    fn from_parts(dir: DirPath, name: FileName, ext: Option[FileExt]) -> FilePath
    fn from_str(s: str) -> Result[FilePath, PathError]

    # Components
    fn dir(self) -> Option[DirPath]
    fn file_name(self) -> Option[FileName]
    fn extension(self) -> Option[FileExt]
    fn drive(self) -> Option[DriveLetter]   # Windows only, None on Unix

    # Operations
    fn join(self, child: FilePath) -> FilePath
    fn parent(self) -> Option[FilePath]
    fn with_extension(self, ext: FileExt) -> FilePath

    # Normalization
    fn normalize(self) -> FilePath          # Resolve . and ..
    fn to_absolute(self) -> Result[FilePath, IoError]

    # Platform conversion
    fn to_native(self) -> str               # Platform-native format
    fn to_posix(self) -> str                # Forward slashes
    fn to_mingw(self) -> str                # C:/path/to/file

    # Validation
    fn exists(self) -> bool
    fn is_file(self) -> bool
    fn is_dir(self) -> bool
    fn is_absolute(self) -> bool
```

### 3.3 Drive Letter Handling (mingw-style)

```simple
# Windows path handling
let win_path = "C:/Users/Public/data.csv"_file

# Access drive
match win_path.drive():
    case Some(d): print f"Drive: {d}"   # "C"
    case None: print "No drive letter"

# Unix paths have no drive
let unix_path = "/home/user/data.csv"_file
assert unix_path.drive().is_none()

# Conversion
let native = win_path.to_native()   # "C:\Users\Public\data.csv" on Windows
let posix = win_path.to_posix()     # "/c/Users/Public/data.csv"
let mingw = win_path.to_mingw()     # "C:/Users/Public/data.csv"
```

### 3.4 File System API

```simple
# std/host/async_nogc/io/fs.spl

# All functions use semantic types - no bare strings!

pub async fn read(path: FilePath) -> Result[Bytes, IoError]
pub async fn read_text(path: FilePath) -> Result[Text, IoError]
pub async fn write(path: FilePath, data: &Bytes) -> Result[ByteCount, IoError]
pub async fn write_text(path: FilePath, text: &Text) -> Result[ByteCount, IoError]

pub async fn create_dir(path: DirPath) -> Result[(), IoError]
pub async fn create_dir_all(path: DirPath) -> Result[(), IoError]
pub async fn remove(path: FilePath) -> Result[(), IoError]
pub async fn remove_dir(path: DirPath) -> Result[(), IoError]
pub async fn rename(from: FilePath, to: FilePath) -> Result[(), IoError]
pub async fn copy(from: FilePath, to: FilePath) -> Result[ByteCount, IoError]

pub async fn exists(path: FilePath) -> bool
pub async fn metadata(path: FilePath) -> Result[FileMetadata, IoError]
pub async fn read_dir(path: DirPath) -> Result[DirEntries, IoError]
```

---

## 4. Network Units

### 4.1 IP Address Unit: `_ip`

IP addresses can be represented in two forms:
1. **String format**: `"127.0.0.1"_ip` - human-readable dotted notation
2. **Numeric format**: `0x7F000001_ip` or `2130706433_ip` - 32-bit integer (IPv4 only)

The grammar already supports both - the type system handles the conversion.

```simple
# std/units/net.spl

# IP address - v4 or v6 (multi-base unit)
# Accepts both string and numeric bases
unit IpAddr: str | u32 as ip

# Specific versions
unit Ipv4Addr: str | u32 as ipv4    # Both "127.0.0.1" and 0x7F000001
unit Ipv6Addr: str | u128 as ipv6   # Both "::1" and numeric

# Port number
unit Port: u16 as port

# Socket address (IP + port)
unit SocketAddr: str as sock

# MAC address (string or 48-bit integer)
unit MacAddr: str | u64 as mac

# Usage - String format (human-readable)
let localhost = "127.0.0.1"_ip
let v6_local = "::1"_ipv6
let addr = "127.0.0.1:8080"_sock
let mac = "00:1A:2B:3C:4D:5E"_mac

# Usage - Numeric format (efficient, no parsing)
let localhost_num = 0x7F000001_ip      # 127.0.0.1 as u32
let localhost_dec = 2130706433_ip      # same as above in decimal
let broadcast = 0xFFFFFFFF_ip          # 255.255.255.255
let port = 8080_port
let mac_num = 0x001A2B3C4D5E_mac       # MAC as 48-bit integer
```

### 4.2 IpAddr API

```simple
impl IpAddr:
    # Construction from components
    fn v4(a: u8, b: u8, c: u8, d: u8) -> Ipv4Addr
    fn v6(segments: [u16; 8]) -> Ipv6Addr
    fn localhost() -> IpAddr
    fn any() -> IpAddr                      # 0.0.0.0

    # Construction from literals (both formats work)
    fn from_str(s: str) -> Result[IpAddr, AddrError]
    fn from_u32(n: u32) -> Ipv4Addr         # For numeric literals
    fn from_u128(n: u128) -> Ipv6Addr       # For IPv6 numeric

    # Properties
    fn is_v4(self) -> bool
    fn is_v6(self) -> bool
    fn is_loopback(self) -> bool
    fn is_private(self) -> bool
    fn is_multicast(self) -> bool

    # Conversion between formats
    fn to_v4(self) -> Option[Ipv4Addr]
    fn to_v6(self) -> Ipv6Addr              # v4-mapped if needed
    fn to_bytes(self) -> Bytes
    fn to_u32(self) -> Option[u32]          # Only for IPv4
    fn to_str(self) -> str                  # Always works

impl Ipv4Addr:
    # Numeric operations (since backed by u32)
    fn octets(self) -> [u8; 4]
    fn to_u32(self) -> u32
    fn from_u32(n: u32) -> Ipv4Addr

impl SocketAddr:
    fn new(ip: IpAddr, port: Port) -> SocketAddr
    fn ip(self) -> IpAddr
    fn port(self) -> Port
```

**How multi-base units work:**

The type `unit IpAddr: str | u32 as ip` means:
- String literals with `_ip` suffix create from string: `"127.0.0.1"_ip`
- Numeric literals with `_ip` suffix create from u32: `0x7F000001_ip`
- The compiler chooses `from_str` or `from_u32` based on literal type
- Both result in the same `IpAddr` type

```simple
# These are equivalent at runtime:
let a = "127.0.0.1"_ip           # Calls IpAddr::from_str("127.0.0.1")
let b = 0x7F000001_ip            # Calls IpAddr::from_u32(0x7F000001)
let c = 2130706433_ip            # Calls IpAddr::from_u32(2130706433)

assert a == b                    # true
assert b == c                    # true
```

### 4.3 TCP/UDP API

```simple
# std/host/async_nogc/net/tcp.spl

pub struct TcpListener:
    fn bind(addr: SocketAddr) -> Result[TcpListener, IoError]
    async fn accept(self) -> Result[(TcpStream, SocketAddr), IoError]
    fn local_addr(self) -> SocketAddr

pub struct TcpStream:
    async fn connect(addr: SocketAddr) -> Result[TcpStream, IoError]
    async fn read(self, buf: &mut Bytes) -> Result[ByteCount, IoError]
    async fn write(self, data: &Bytes) -> Result[ByteCount, IoError]
    async fn shutdown(self) -> Result[(), IoError]
    fn peer_addr(self) -> SocketAddr
    fn local_addr(self) -> SocketAddr

# std/host/async_nogc/net/udp.spl

pub struct UdpSocket:
    fn bind(addr: SocketAddr) -> Result[UdpSocket, IoError]
    async fn recv_from(self, buf: &mut Bytes) -> Result[(ByteCount, SocketAddr), IoError]
    async fn send_to(self, data: &Bytes, addr: SocketAddr) -> Result[ByteCount, IoError]
    fn local_addr(self) -> SocketAddr
```

---

## 5. HTTP Units

### 5.1 HTTP URL Unit: `_http`

```simple
# std/units/url.spl

# Generic URL
unit Url: str as url

# Protocol-specific URLs
unit HttpUrl: str as http       # http:// or https://
unit FtpUrl: str as ftp         # ftp://
unit FileUrl: str as fileurl    # file://

# URL components
unit Scheme: str as scheme      # "http", "https", "ftp"
unit Host: str as host          # domain or IP
unit UrlPath: str as urlpath    # path component
unit Query: str as query        # query string
unit Fragment: str as fragment  # fragment/anchor

# Usage
let api = "https://api.example.com/v1/users"_http
let download = "ftp://files.example.com/data.zip"_ftp
let local = "file:///home/user/doc.pdf"_fileurl
```

### 5.2 Url API

```simple
impl Url:
    # Construction
    fn from_str(s: str) -> Result[Url, UrlError]
    fn builder() -> UrlBuilder

    # Components
    fn scheme(self) -> Scheme
    fn host(self) -> Option[Host]
    fn port(self) -> Option[Port]
    fn path(self) -> UrlPath
    fn query(self) -> Option[Query]
    fn fragment(self) -> Option[Fragment]
    fn username(self) -> Option[str]
    fn password(self) -> Option[str]

    # Operations
    fn join(self, path: UrlPath) -> Url
    fn with_query(self, query: Query) -> Url
    fn with_fragment(self, fragment: Fragment) -> Url

struct UrlBuilder:
    fn scheme(self, s: Scheme) -> UrlBuilder
    fn host(self, h: Host) -> UrlBuilder
    fn port(self, p: Port) -> UrlBuilder
    fn path(self, p: UrlPath) -> UrlBuilder
    fn query_param(self, key: str, value: str) -> UrlBuilder
    fn build(self) -> Result[Url, UrlError]
```

### 5.3 HTTP Client API

```simple
# std/host/async_nogc/net/http.spl

# HTTP method enum
enum HttpMethod:
    Get
    Post
    Put
    Delete
    Patch
    Head
    Options

# HTTP status code
unit StatusCode: u16 as status

# HTTP header
unit HeaderName: str as header
unit HeaderValue: str as hval

pub struct HttpRequest:
    fn new(method: HttpMethod, url: HttpUrl) -> HttpRequest
    fn get(url: HttpUrl) -> HttpRequest
    fn post(url: HttpUrl) -> HttpRequest
    fn header(self, name: HeaderName, value: HeaderValue) -> HttpRequest
    fn body(self, data: Bytes) -> HttpRequest
    fn json[T: Serialize](self, value: &T) -> HttpRequest
    fn timeout(self, duration: Duration) -> HttpRequest

pub struct HttpResponse:
    fn status(self) -> StatusCode
    fn header(self, name: HeaderName) -> Option[HeaderValue]
    fn headers(self) -> Headers
    async fn body(self) -> Result[Bytes, IoError]
    async fn text(self) -> Result[Text, IoError]
    async fn json[T: Deserialize](self) -> Result[T, JsonError]

pub struct HttpClient:
    fn new() -> HttpClient
    fn with_timeout(timeout: Duration) -> HttpClient
    async fn send(self, request: HttpRequest) -> Result[HttpResponse, HttpError]

    # Convenience methods
    async fn get(self, url: HttpUrl) -> Result[HttpResponse, HttpError]
    async fn post(self, url: HttpUrl, body: Bytes) -> Result[HttpResponse, HttpError]

# Usage
let client = HttpClient::new()
let response = await client.get("https://api.example.com/users"_http)?
let status = response.status()
let body = await response.json[UserList]()?
```

---

## 6. FTP Units

### 6.1 FTP URL Unit: `_ftp`

```simple
# std/units/url.spl (addition)

unit FtpUrl: str as ftp

impl FtpUrl:
    fn from_str(s: str) -> Result[FtpUrl, UrlError]
    fn host(self) -> Host
    fn port(self) -> Port               # Default 21
    fn path(self) -> UrlPath
    fn username(self) -> Option[str]
    fn password(self) -> Option[str]
```

### 6.2 FTP Client API

```simple
# std/host/async_nogc/net/ftp.spl

# FTP transfer mode
enum TransferMode:
    Binary
    Ascii

# FTP file type
enum FtpFileType:
    File
    Directory
    Link

pub struct FtpClient:
    async fn connect(url: FtpUrl) -> Result[FtpClient, FtpError]
    async fn connect_with_creds(
        host: Host,
        port: Port,
        username: str,
        password: str
    ) -> Result[FtpClient, FtpError]

    # Navigation
    async fn pwd(self) -> Result[UrlPath, FtpError]
    async fn cd(self, path: UrlPath) -> Result[(), FtpError]
    async fn cdup(self) -> Result[(), FtpError]
    async fn list(self) -> Result[Array[FtpEntry], FtpError]

    # Transfer
    async fn download(self, remote: UrlPath, local: FilePath) -> Result[ByteCount, FtpError]
    async fn upload(self, local: FilePath, remote: UrlPath) -> Result[ByteCount, FtpError]
    async fn download_bytes(self, remote: UrlPath) -> Result[Bytes, FtpError]
    async fn upload_bytes(self, data: &Bytes, remote: UrlPath) -> Result[ByteCount, FtpError]

    # File operations
    async fn delete(self, path: UrlPath) -> Result[(), FtpError]
    async fn mkdir(self, path: UrlPath) -> Result[(), FtpError]
    async fn rmdir(self, path: UrlPath) -> Result[(), FtpError]
    async fn rename(self, from: UrlPath, to: UrlPath) -> Result[(), FtpError]

    # Settings
    fn set_transfer_mode(self, mode: TransferMode) -> FtpClient
    fn set_passive(self, passive: Enabled) -> FtpClient

    # Disconnect
    async fn quit(self) -> Result[(), FtpError]

pub struct FtpEntry:
    fn name(self) -> FileName
    fn file_type(self) -> FtpFileType
    fn size(self) -> Option[ByteCount]
    fn modified(self) -> Option[DateTime]
    fn permissions(self) -> Option[FilePermissions]
```

---

## 7. Complete Unit Postfix Summary

### 7.1 All Standard Unit Postfixes

| Category | Unit Type | Postfix | Example |
|----------|-----------|---------|---------|
| **IDs** | UserId | `_uid` | `42_uid` |
| | SessionId | `_sid` | `1001_sid` |
| | RequestId | `_rid` | `req_rid` |
| **Files** | FilePath | `_file` | `"/path/to/file"_file` |
| | FileName | `_filename` | `"config"_filename` |
| | FileExt | `_ext` | `"json"_ext` |
| | DirPath | `_dir` | `"/home/user"_dir` |
| | DriveLetter | `_drive` | `"C"_drive` |
| **Network** | IpAddr | `_ip` | `"127.0.0.1"_ip` |
| | Ipv4Addr | `_ipv4` | `"192.168.1.1"_ipv4` |
| | Ipv6Addr | `_ipv6` | `"::1"_ipv6` |
| | Port | `_port` | `8080_port` |
| | SocketAddr | `_sock` | `"127.0.0.1:8080"_sock` |
| | MacAddr | `_mac` | `"00:1A:2B:3C:4D:5E"_mac` |
| **URLs** | Url | `_url` | `"https://example.com"_url` |
| | HttpUrl | `_http` | `"https://api.example.com"_http` |
| | FtpUrl | `_ftp` | `"ftp://files.example.com"_ftp` |
| | FileUrl | `_fileurl` | `"file:///path"_fileurl` |
| | Scheme | `_scheme` | `"https"_scheme` |
| | Host | `_host` | `"example.com"_host` |
| | UrlPath | `_urlpath` | `"/api/v1"_urlpath` |
| | Query | `_query` | `"key=value"_query` |
| **HTTP** | StatusCode | `_status` | `200_status` |
| | HeaderName | `_header` | `"Content-Type"_header` |
| | HeaderValue | `_hval` | `"application/json"_hval` |
| **Size** | ByteCount | `_bytes` | `1024_bytes` |
| | KiloBytes | `_kb` | `64_kb` |
| | MegaBytes | `_mb` | `512_mb` |
| | GigaBytes | `_gb` | `4_gb` |
| **Time** | Duration | `_dur` | (use time units) |
| | Milliseconds | `_ms` | `100_ms` |
| | Seconds | `_s` | `30_s` |
| | Minutes | `_min` | `5_min` |
| **Physical** | Meters | `_m` | `100_m` |
| | Kilometers | `_km` | `5_km` |
| | Kilograms | `_kg` | `70_kg` |

### 7.2 Compound Literal Rules

```simple
# Numeric postfixes (no underscore between number and suffix)
let port = 8080_port
let size = 1024_bytes
let count = 42_uid

# String postfixes (literal string with postfix)
let path = "/home/user"_file
let ip = "192.168.1.1"_ip
let url = "https://example.com"_http

# Combining with string interpolation
let api = f"https://api.{domain}"_http  # ERROR: no postfix on f-strings
let api = HttpUrl::from_str(f"https://api.{domain}")?  # OK
```

---

## 8. Updated Spec Changes

### 8.1 New Lint: `bare_string`

Add to `doc/spec/units.md`:

```markdown
### 8.1 The `bare_string` Lint

**Problem**: Bare `str`/`String` types are too generic for semantic APIs.

**Solution**: The `bare_string` lint warns when `str` or `String` appears in public function signatures.

**Levels:**
- `warn` (default) - Emit warning
- `deny` - Treat as compile error
- `allow` - Suppress

**Standard Library Policy:**
```simple
# std/__init__.spl
#[deny(primitive_api)]
#[deny(bare_string)]     # All string types must be semantic
mod std
```

**Exemptions** (`#[allow(bare_string)]`):
- `std.fmt` - formatting arbitrary values
- `std.log` - logging messages
- Low-level string parsing utilities
```

### 8.2 String Postfix Extension

Add to `doc/spec/syntax.md`:

```markdown
### String Literal Postfixes

String literals can have unit postfixes for semantic typing:

```simple
# Syntax: "string"_suffix
let path = "/home/user/file.txt"_file
let ip = "192.168.1.1"_ip
let url = "https://example.com"_http
```

**Lexer rule:**
```
STRING_UNIT = STRING_LITERAL "_" IDENTIFIER
```

**Note**: F-strings cannot have postfixes. Use explicit conversion:
```simple
# ERROR
let url = f"https://{host}"_http

# OK
let url = HttpUrl::from_str(f"https://{host}")?
```
```

### 8.3 Updated Type Warning Table

Update `doc/spec/units.md`:

```markdown
| Type | In Public API | Lint |
|------|---------------|------|
| `i8`..`i64`, `u8`..`u64`, `f32`, `f64` | WARNING | `primitive_api` |
| `bool` | WARNING | `bare_bool` |
| `str`, `String` | WARNING | `bare_string` |
| `Option[T]` | OK | - |
| `Result[T, E]` | OK | - |
| Unit types (`UserId`, `FilePath`, etc.) | OK | - |
| Enums | OK | - |
```

---

## 9. Implementation Features

### Feature List

| # | Feature | Importance | Difficulty | Dependencies |
|---|---------|------------|------------|--------------|
| 200 | `bare_string` lint | High | Medium | Lint infrastructure |
| 201 | String literal postfixes in lexer | High | Low | Lexer |
| 202 | FilePath unit type | High | Medium | Units core |
| 203 | Drive letter support (mingw) | Medium | Medium | FilePath |
| 204 | IpAddr unit type | High | Medium | Units core |
| 205 | Port unit type | High | Low | Units core |
| 206 | SocketAddr unit type | High | Medium | IpAddr, Port |
| 207 | Url unit type | High | Medium | Units core |
| 208 | HttpUrl unit type | High | Low | Url |
| 209 | FtpUrl unit type | Medium | Low | Url |
| 210 | TCP async API | High | High | async runtime, net FFI |
| 211 | UDP async API | High | Medium | async runtime, net FFI |
| 212 | HTTP client | High | High | TCP, TLS |
| 213 | FTP client | Medium | High | TCP |
| 214 | StatusCode unit | Medium | Low | Units core |
| 215 | HeaderName/Value units | Medium | Low | Units core |
| 216 | ByteCount unit family | High | Low | Units core |
| 217 | async_nogc default profile | High | Low | Profile system |
| 218 | File system async API | High | High | async runtime, fs FFI |

### Implementation Order

**Phase 1: Core Units (Sprint 1)**
1. Feature 201: String literal postfixes in lexer
2. Feature 200: `bare_string` lint
3. Feature 202: FilePath unit type
4. Feature 203: Drive letter support
5. Feature 216: ByteCount unit family

**Phase 2: Network Units (Sprint 2)**
1. Feature 204: IpAddr unit type
2. Feature 205: Port unit type
3. Feature 206: SocketAddr unit type
4. Feature 207: Url unit type
5. Feature 208: HttpUrl unit type
6. Feature 209: FtpUrl unit type

**Phase 3: Network APIs (Sprint 3)**
1. Feature 217: async_nogc default profile
2. Feature 210: TCP async API
3. Feature 211: UDP async API

**Phase 4: High-Level Protocols (Sprint 4)**
1. Feature 218: File system async API
2. Feature 212: HTTP client
3. Feature 214-215: HTTP header units
4. Feature 213: FTP client

---

## 10. Native Library Support

### 10.1 native_lib/io/net.rs

```rust
// TCP
pub extern "C" fn native_tcp_bind(addr: *const c_char, port: u16) -> i64;
pub extern "C" fn native_tcp_accept(listener: i64) -> i64;
pub extern "C" fn native_tcp_connect(addr: *const c_char, port: u16) -> i64;
pub extern "C" fn native_tcp_read(stream: i64, buf: *mut u8, len: usize) -> isize;
pub extern "C" fn native_tcp_write(stream: i64, buf: *const u8, len: usize) -> isize;
pub extern "C" fn native_tcp_close(handle: i64);

// UDP
pub extern "C" fn native_udp_bind(addr: *const c_char, port: u16) -> i64;
pub extern "C" fn native_udp_recv_from(socket: i64, buf: *mut u8, len: usize, addr_out: *mut c_char) -> isize;
pub extern "C" fn native_udp_send_to(socket: i64, buf: *const u8, len: usize, addr: *const c_char, port: u16) -> isize;
pub extern "C" fn native_udp_close(handle: i64);
```

### 10.2 Async Integration

The async runtime uses platform-specific I/O:
- **Linux**: io_uring or epoll
- **macOS**: kqueue
- **Windows**: IOCP

```rust
// native_lib/io/async_io.rs
pub extern "C" fn native_async_tcp_read(stream: i64, buf: *mut u8, len: usize, callback: extern "C" fn(isize));
pub extern "C" fn native_async_tcp_write(stream: i64, buf: *const u8, len: usize, callback: extern "C" fn(isize));
```

---

## Related Documents

- [Unit Types Specification](../spec/units.md)
- [Standard Library Specification](../spec/stdlib.md)
- [Import/Export and __init__](../spec/modules.md)
- [Concurrency Specification](../spec/concurrency.md)
