# `src/lib/nogc_async_mut/io/scatter_gather.spl`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0011"></a>FR-NET-0011 | Add scatter-gather I/O list types | Provide `IoVec` (buffer_id, offset, len) and `ScatterGatherList` types mirroring POSIX iovec so that send/recv paths can describe discontiguous buffer regions without copying into a single allocation. Include a byte-boundary split helper fo | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
