# Full CLI low-memory compilation retains the parser closure

Status: focused source repair authored; corrected-producer execution and full
CLI memory qualification remain pending.

The attempt2 full CLI owner used the admitted Pure-Simple compiler with LLVM,
`--low-memory`, one thread and the Windows MSVC target. Its retained log is
`C:/dev/simple-phase3-bootstrap-evidence/attempt2/cli-hir-rss-failure.log`.
It collected 2545 source files, emitted `surface_build` and `surface_alias`
progress, and entered HIR with the retained parser route. The last progress
row reports 85/2545 modules and `compiler.driver.driver_types` at 721893 ms.
The resource owner exited 88 at 5865052 KiB peak RSS against 5859375 KiB.
There was no durable per-file memory snapshot in that attempt. These facts
establish the failed route and total peak, not a measured allocation breakdown.

`driver_streaming_surface_route` previously consulted environment requests
only. `CompileOptions.low_memory` did not request the existing per-file parse,
compact surface, reparse-and-lower ownership route. Consequently low-memory
entry builds could hold the complete parsed closure and compact surfaces while
adding HIR roots. Existing per-file HIR scratch scopes cannot reclaim those
phase-2 retained parser owners.

The repair requests streaming for low-memory AOT entry compilation when the
existing route supports all consumers. It preserves the retained route for
interpretation, missing entry authority, coverage, MC/DC and VHDL. Explicit
streaming environment requests retain their existing rejection codes. It
changes no source inventory, import closure, parser semantics or RSS limit.

`test/01_unit/compiler/driver/low_memory_streaming_request_spec.spl` exercises
route selection and each incompatible consumer. Its execution is pending a
qualified Pure-Simple test runner. A current-producer diagnostic with the
existing streaming environment opt-in can measure that ownership route, but
cannot admit this source change. Acceptance requires rebuilding the producer,
compiling its complete CLI with the original inventory and resource controls,
and recording comparable peak RSS and elapsed time plus actual CLI behavior.

The standalone native fixture
`test/fixtures/compiler/low_memory_streaming_request/main.spl` passed with the
admitted producer SHA256
`1ad6ea53c67f3e01efc5c1b0ac8aa4dcef184a0987b4d3c806c59e14e96be584`.
It compiled two actual modules with LLVM for Windows MSVC; the compile owner
reported exit 0, 45088 ms compiler elapsed and 287608 KiB peak RSS. The resulting
executable SHA256
`81a3eec4a4e31876aead5acc0fe5885f429fbce4a8da23138f4e950f14bc5c25`
ran with exit 0 and `low-memory streaming policy: 11 checks passed`. Evidence is
retained under `C:/dev/simple-phase3-hir-memory-evidence/policy-probe*`, with
600 seconds and 5859375 KiB enforced. This confirms the policy helper's native
behavior. It does not execute a rebuilt driver, the SSpec suite or the full CLI,
and no comparable baseline establishes a memory improvement yet.

## Current-producer streaming diagnostics

Two separately retained positional full-CLI attempts used the admitted producer
above, explicit `SIMPLE_STAGE3_STREAMING_SURFACES=1`, private caches/storage and
the original CLI entry. Both enforced 600 seconds and 5859375 KiB; neither
compiled a rebuilt driver.

The first attempt retained only 2409 closure sources and exited 1 during source
loading because sparse checkout omitted the backend registry/VHDL plugin source
owners. Its peak was 537560 KiB. It is missing-input evidence, not a memory
result. Evidence: `C:/dev/simple-phase3-hir-memory-evidence/full-cli-streaming/`.

After materializing all `src`, the fresh second attempt selected streaming
ownership and parsed, promoted and released all 2517 physical source surfaces.
It then timed out with exit 124 at the export-origin/freeze boundary, before HIR
opened its durable snapshot or an executable existed. Its enforced resource
receipt reports peak RSS 1506780 KiB. Exact source HEAD/tree/status/patch,
producer/script hashes and the SIMPLE environment are retained in
`C:/dev/simple-phase3-hir-memory-evidence/full-cli-streaming-attempt2/`.

The original retained-route log contains 2545 distinct parsed source paths.
The second streaming log contains 2517. Comparing those observed paths finds
29 original-only paths in `src/app/cmm_lsp` (8), `src/app/mcp_t32` (13) and
`src/app/t32_cli` (8), and one streaming-only path `src/app/__init__.spl`.
This is consistent with differing configured alias materialization; observed
path lists do not establish source-byte or SCV manifest equivalence. The
diagnostic cannot prove improvement on the identical required inventory or
admit the full CLI. No third automatic rerun was performed. A corrected source
snapshot must materialize and bind the configured aliases before qualification.
