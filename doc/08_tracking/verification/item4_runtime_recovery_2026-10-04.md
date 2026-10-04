# Item4 runtime recovery evidence

STATUS: FAIL — full linker/Phase 4 and five-host qualification remain open.

This lane investigates the actual execution prerequisite instead of treating
more authored linker scenarios as executed evidence. The old three-attempt
probe cap was preserved. No bootstrap was restarted, no Rust seed was used for
tests, and no independently owned process or mutable cache was changed.

A newer retained-object pure-Simple compiler has a recorded Hello compile/run
PASS but is explicitly unadmitted. Its independent full-CLI and test-runner
jobs were still live without usable executables at inspection. Exact paths,
digests and point-in-time process evidence are appended to the original
`item4_source_inventory_cold_init_timeout_2026-10-03.md` bug report. Summary
aggregates can contain older attempts and are not current completion receipts.

Revalidation at 2026-10-04 20:47 +09:00 found full-CLI owner 64728 and
collector 34464 no longer live. Its attempt-specific
`phase34-post-link4/cranelift/phase4-full-cli/artifact/result.json` records
`exit_code: 1`, `compile_exit: 1`, `artifact_sha256: null`, `admitted: false`.
The separate test-runner owner 37596 and collector 22612 were still live at
that observation. This terminal full-CLI failure does not justify a restart or
establish that the loader-only repair resolves all reported compilation errors.

Actual fatal log diagnostics identify three module-loader calls to helpers
absent from its imported implementation module. Intent 9db11f8734e exercises
real generic-name identity before repair 1adc1bff730 replaces those calls with
the exact collection operations used by the compatibility helper bodies.
Independent source review found no concrete P0/P1. This does not establish that
the other bootstrap failures are fixed or that JIT paths have executed.

Fifteen linker manuals now require explicit LLVM AOT, pinned producer identity,
retained artifacts and nonvacuous scenario evidence. Their 121 declarations are
source counts, not execution or individual assertion counts. Existing explicit
MCP interpreter requirements were not changed. The active runner's generated
temporary entry and restricted source list expose a separate admission gap;
its controlled generated-source/snapshot design remains implementation work.

Simple compilation, native tests, doctests/docgen, coverage, compiler/lib/MCP/LSP
checks, native smoke and performance checks remain UNRUN. No formal readiness
PASS, executable deployment, release tag or publication is claimed.

Scoped source checks against base `9af9a8c0c70c4a04f6fc3a5bac7db475362854f5`
passed whitespace, direct-env runtime guards (working/staged), and numbered
artifact classification (six classified paths, zero numbered artifacts).
`doc/06_spec` contains zero executable `_spec.spl` files. Test-tree delta
verification reports 3152 pre-existing offenders and zero introduced; it does
not establish a clean repository-wide test tree. The recorded offender list is
`C:/dev/simple/.git/item4-runtime-recovery-preexisting-offenders.txt`, SHA256
`2fb68a47bab7953e058a449562ecba2df9f135b8d2e2d99c3e14f373b1c1d719`.
These structural checks do not replace the unrun runtime gates above.
