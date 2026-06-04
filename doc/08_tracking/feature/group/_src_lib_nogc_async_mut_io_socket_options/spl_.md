# `src/lib/nogc_async_mut/io/socket_options.spl`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0012"></a>FR-NET-0012 | Add async TCP socket option record types | Mirror and extend the sync Nagle/keepalive helpers from `nogc_sync_mut/tcp/socket.spl` into a comprehensive `TcpSocketOptions` record covering nodelay, cork, quickack, keepalive (idle/interval/count), SO_LINGER, and sndbuf/rcvbuf. Provide n | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
