# static

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-STATIC_FILE_COMPRESSION_CACHE_INTEGRATION_2026_05_01"></a>STATIC_FILE_COMPRESSION_CACHE_INTEGRATION_2026_05_01 | Wire StaticCompressionCache into StaticFileHandler.handle() | **Status: LANDED 2026-05-01** — `StaticFileHandler.handle()` now consults a default-constructed `StaticCompressionCache` for files <= 64 KiB; cache miss compresses + stores, cache hit serves bytes with `Content-Encoding` + `Vary: Accept-Enc | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
