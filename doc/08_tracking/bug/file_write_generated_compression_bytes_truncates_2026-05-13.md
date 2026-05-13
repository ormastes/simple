# File Write Truncates Generated Compression Byte Buffers

Date: 2026-05-13
Status: Open

Host-tool compatibility checks for generated zstd/xz buffers exposed a file-write seam: `rt_file_write_bytes(path, encoded)` wrote only a truncated payload for buffers returned by the pure compression encoders. One observed zstd frame file contained a single byte (`0x0c`), causing host `zstd` to report `unknown header` even though in-process decode of the same generated buffer succeeded.

Current handling: compression framework and zstd frame specs assert in-process encode/decode compatibility for these generated buffers. Host decode coverage remains available for host-generated input fixtures that are read with `rt_file_read_bytes`.

Next step: isolate whether `rt_file_write_bytes` mishandles generated `[u8]` arrays, typed byte arrays, or arrays returned through facade/module boundaries, then restore host zstd/xz emitted-stream checks.
