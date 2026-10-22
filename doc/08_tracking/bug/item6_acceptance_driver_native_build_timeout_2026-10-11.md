# Item 6 acceptance driver: bounded native build timeout

Status: OPEN diagnostic blocker; canonical bug-DB reconciliation pending.
This is not an admitted compiler regression or an Item 6 performance result.

Source: `57da5af7ec31af047d4fce97e9e6a0aec4a0b475` on the isolated
`work/item6-phase3-validation-20261011` branch. Target: `release_phase3`.
Entry: `src/app/test/package_index_acceptance.spl`.
Compiler: pure-Simple diagnostic Phase 2 producer, SHA-256
`b580919372e209ea2a10e6d8e919b0f90c5dc3100e76f958f584c5db0ace4778`.
Its successful LLVM hello evidence is minimum diagnostic sanity, not formal
bootstrap admission. Compiler bytes matched before and after this probe.

The native-build request selected LLVM/MSVC, `core-c-bootstrap`, this worktree's
runtime, `--source src --entry-closure`, two workers, enabled frontend/HIR
caches, an isolated acceptance-entry cache and disabled Rust delegation/stub
fallback. No compatible idle cache for this entry/source/runtime was found;
no other lane's mutable cache was copied, cleared or rewritten. Four unrelated
Rust bootstrap processes were active, so this is not a quiet-runner benchmark.

The first two collector envelopes refused before spawning because their
arguments and storage layout did not match the collector contract. The corrected
third invocation launched one supervised build, then stopped at 240 seconds.
Receipt: `status=complete`, `reason=timeout`, native exit 124,
`cleanup_status=reaped`, `final_job_active=0`, sampled/enforced 4 GiB RSS cap,
peak 440008 KiB, no RSS observer error. Only 71 log bytes were captured: the
existing incomplete-workaround-coverage advisory. No executable was produced;
no owner or system scenario ran. The external controller exit is 1 and does
not replace the receipt's underlying timeout status.

Evidence is retained at
`C:/dev/simple-bootstrap-storage/item6-phase3-validation-20261011/acceptance-probe/`:
`request.json`, `status.env`, `logs/build.log`, and `logs/receipt.env`.
The reviewed controller is the sibling `build-acceptance-probe.ps1`.
Limits additionally bound logs to 8 MiB, artifact growth to 2 GiB and free disk
to a 3 GiB floor. Do not rerun this stopped three-attempt cycle or discard its
cache. No source fix, compiler-phase localization or increased budget is
established by this observation.

Resolution requires an admitted usable compiler or a separately scoped,
instrumented diagnosis locating the slow/failing compilation stage, followed
by real acceptance-entry execution with nonzero scenario counts. Keep the
44-scenario system, generated-producer authority, bootstrap/full-CLI,
core/MCP/LSP and clean/warm/no-op/edit performance gates unresolved meanwhile.
