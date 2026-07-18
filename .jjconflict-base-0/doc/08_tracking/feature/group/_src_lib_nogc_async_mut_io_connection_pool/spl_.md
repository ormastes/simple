# `src/lib/nogc_async_mut/io/connection_pool.spl`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0013"></a>FR-NET-0013 | Add TCP connection pool for HTTP keep-alive reuse | Provide a pure Simple connection pool keyed by host:port that tracks idle file descriptors with timestamps, enforces max-idle-per-host, and exposes acquire/release/evict-expired operations. Pool stats (acquired, released, evicted) must be i | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
