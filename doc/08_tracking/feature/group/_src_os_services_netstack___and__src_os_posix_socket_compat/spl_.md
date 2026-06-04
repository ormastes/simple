# `src/os/services/netstack/`_and_`src/os/posix/socket_compat.spl`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0001"></a>FR-NET-0001 | Add connect completion and nonblocking socket semantics | `connect()` must not report a completed TCP connection until the 3-way handshake reaches `ESTABLISHED`. Blocking sockets should wait or sleep on a bounded completion path; nonblocking sockets should return an errno-style in-progress result  | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
