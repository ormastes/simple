# Seed `run` segfaults (rc 139) on a probe importing the COFF linker

- **Status:** open
- **Component:** Rust seed interpreter (`bin/simple.exe run`)
- **Found:** 2026-10-27, Windows x86_64

## Repro

Seed binary `C:/dev/simple/bin/simple.exe` (md5 prefix `735d9bd027fe`), cwd a
`release/1.0.0` checkout. A probe of ~50 lines whose only imports are

```
use std.io_runtime.{file_read, file_read_bytes, file_write_bytes, file_exists, env_get}
use compiler.backend.linker.coff.coff_link.{CoffLinkRequest, coff_link_default_libraries, coff_link_amd64_retained_image_policy_full}
use compiler.backend.linker.coff.pe_image_writer.{PeImagePolicy}
```

```
bin/simple.exe run probe.spl
```

exits **139 (SIGSEGV) after 8 s** with no output; the last log line is an
`[engine-demotion] reason=hybrid-interp-splice` row. The same source built with
`stage2.exe native-build` runs correctly, and `bin/simple.exe test` runs specs
importing the same modules, so only the `run` path is affected.

## Impact

`run` cannot be used to exercise the pure-Simple linker; the workaround is a
native-built probe (stage2 `native-build`, ~200 s) under a memory cap.
