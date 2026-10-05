# Native access violation after clean HIR lowering

Status: reproducible native failure; failing operation not yet identified.
This checkpoint adds diagnostic boundaries, not a memory-safety fix. No compiler
or debugger was launched for this source-only investigation.

The retained `p3-next9d484-cranelift80-startup3/owner/build.log` has SHA-256
`c35fb49ed3ead0608bb2ee5c3dae32fb4eaa77910c7ca76a5fcf3762ab6525e2`.
Its worker completes 1,138 HIR modules with zero failures, zero cache hits and
1,138 stores, then exits with raw status `-1073741819` (`0xc0000005`, Windows
access violation). The outer invocation exits 139 and emits no compiler binary.
Target source is `9d484080c34c6e52ea001c5231c0f62bc0e383ea`; producer SHA-256 is
`0fce5d949d48b1a924c8131cc496ec191c8fce43033dbdc793386d819cc61e99`, built from
`20975fbf9eb33336b6f938b2e9c2b6d89fed70d3` and separately relinked with the real
Windows system-library providers. HIR completion is not full compilation PASS.

The earlier `test-runner-post-hir-crash-repro1` reproduces the same raw exception
after 660 clean HIR modules under producer `776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40`
and source `9737d1217bc44439b56bba6c2ef16faaff51bd20`.
Its retained phase markers prove context publication, value-struct validation,
dictionary census, layer equality, effects, aspects and advice weaving completed.
The final marker is `phase3:hir:validate:done errors=0`. This rules out those
operations as the immediate fault in that run, but does not rule out earlier
memory corruption. The P3 run did not enable the same detailed profile; it is
not evidence that its failing operation is identical.

The remaining unobserved region contains the post-validation error-count read,
typecheck severity lookup/optional typecheck, safety severity lookup/optional
safety, unconditional Any-escape and enum-contract passes, and cold HIR receipt
capture. No evidence presently singles out one of these as the memory defect.

`driver_hir_pipeline_lowering.spl` now uses the existing phase-profile owner to
record literal start/done boundaries around those calls. Failed and skipped
cold-receipt paths remain distinguishable. The existing streaming path gets the
same cold-receipt boundaries. All checks, severity choices, diagnostics and
failure returns remain active. Profiling remains opt-in through the existing
owner; no new environment transport or unconditional per-module output is added.

For a future authorized native verification, retain the real worker stdout and
stderr, exact producer/source/cache identity, final phase boundary, raw exit and
owned process-tree closure. A start without a done narrows the fault location;
neither a marker nor a cache store qualifies the build. This checkpoint has no
native execution evidence and does not authorize another compiler run.

There is also a separate reporting defect in `native_build_main.spl`: the
`code < -128` branch treats signed Windows exception codes as POSIX
`-(128 + signal)`, printing the impossible signal `1073741691`. The arithmetic
exactly explains the misleading KILLED message; it is not evidence of an
external kill. That classifier is unchanged here, and fixing it alone cannot
repair the access violation.
