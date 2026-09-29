# Stage4 positional AOT source-owner copy emptied the no-op receipt path

- **Status:** Fixed for the tested Stage4 hello path
- **Found:** 2026-09-29, Linux ARM64 exact Stage4 standalone compiler
- **Impact:** before the fix, compiler exited 1 after linking a runnable hello

After the backend lease receiver fix, the exact Stage4 compiler compiled one
hello module, linked a 21,448-byte ARM64 executable, and that executable ran
and printed `Hello World`. The compiler nevertheless returned
`native no-op receipt publication failed: receipt-invalid` after the link.

The publication path was traced once. `native_noop_publish_fault_built_v1`
reached `native_noop_encode_v1` with `sources=0` and a nonempty request
identity. That encoder correctly refuses an empty source inventory. The
temporary print was removed. `load_sources_impl` assigns
`self.ctx.source_paths_owner` from the loaded sources. The publisher reads a
one-slot vector whose only path is empty; source validation then yields zero
usable paths. The bad text is pinned to the owner-copy operation, before the non-streaming context
assignment: a bounded trace showed the loaded hello path at length 51 while
`driver_source_owner_text_copy(loaded_source.path)` immediately returned
length 0. The one-slot owner vector stayed present through publication, but
its only string was empty. The copy helper currently uses
`rt_bytes_to_text(value.bytes())`; this native-compiled path did not preserve
the input text. Temporary trace prints were removed.

The helper now uses `rt_string_substr_from(value, 0)`, which makes one owned
runtime string copy without building an intermediate byte array. The exact
Stage4 compiler rebuilt 866 units without failure. Hello AOT returned exit 0,
wrote a 21,448-byte ARM64 executable, and that executable printed
`Hello World` with exit 0. Receipt publication therefore accepted the
source inventory in this path. A second identical build returned exit 0 but
did not hit no-op admission; that performance issue is tracked separately.
The matched C size ratio and production startup/RSS receipts remain open.

Evidence: `build/mini_builds/target5_stage4_lease_unique_build.log`,
`target5_stage4_lease_unique_hello.log`, and
`target5_stage4_noop_trace_hello.log`. The loader-boundary proof is in
`target5_stage4_owner_copy_trace_hello.log`.
The successful build is in `target5_stage4_owner_substr_build.log` and
`target5_stage4_owner_substr_hello.log` under `build/mini_builds/`.
