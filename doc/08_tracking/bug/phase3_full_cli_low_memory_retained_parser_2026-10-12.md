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
