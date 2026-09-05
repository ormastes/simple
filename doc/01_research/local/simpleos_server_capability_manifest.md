# SimpleOS server capability manifest — local research

The canonical contract already exists in
`src/lib/common/contracts/execution/simpleos_capability_v1.spl`, but the HTTP
ALPN path selected from a private literal list and the SSH daemon published no
manifest. The reachable owners are the async HTTP worker dispatch for
`http/1.1` and `h2`, and the SimpleOS SSH session plus authenticated SFTP v3
subsystem. Generic HTTP WebSocket upgrade is not owned by that HTTP server;
HTTP/3 framing has no reachable QUIC transport; WebTransport has no production
session owner. The fix must therefore centralize reachability without adding
another wire stack.
