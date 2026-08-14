# Compiler, loader, script, and cross-language performance

Status: focused source contract; retained runtime timing remains open. Failed
existence-probe evidence is now an executable deterministic gate, not syscall
evidence.

Executable source: `test/05_perf/compiler_loader_script_crosslang_perf_spec.spl`.

## Operator flow

Run the scenarios through the admitted self-hosted CLI and follow the manual
steps in this order:

1. Check two deterministic missing facade calls.
2. Prepare equivalent performance fixtures.
3. Verify optimized paths preserve behavior and budgets.
4. Measure failed existence probes at the file-exists facade.
5. Audit C, Rust, and interpreter-provider probe contracts.
6. Reject a preexisting fixture without deleting any path.
7. Admit executable identity and execution modes.
8. Compare cross-language semantic parity.
9. Measure compiler loader and script rows.

The canonical plan contains exact commands and the blocker/resume ledger:
`doc/03_plan/sys_test/compiler_loader_script_crosslang_perf.md`. A source-only
contract pass does not close retained timing/RSS, foreign capability lifetime,
compiler/MCP/LSP, or Stage 4 identity gates.

Only this plan-facing summary/disposition is updated. The generated mirror/manual
remains **BLOCKED**: this file is not a fresh docgen artifact and does
not yet carry generated per-scenario sections, source hash/provenance, folded
executable source, or a `0 stubs` receipt. Regenerate it only after an admitted
self-hosted CLI is available, then have the final reviewer read the generated
manual again for final readability before calling it complete.

## Troubleshooting

- Missing `bin/release/<triple>/simple`: record the Stage 4 prerequisite and
  stop; never substitute `src/compiler_rust/target/bootstrap/simple`.
- Missing `check-compiler-loader-perf.shs` or
  `check-interpreter-packed-byte-rss.shs`: those historical helpers are absent
  on current `main`; use the existing checker paths in the canonical plan.
- A focused failure after three distinct fix/verify cycles: retain the log,
  update the blocker ledger, and stop instead of rerunning the same command.
- A counter result is facade evidence only; do not label it a syscall count.

The spec proves exact repeated negative-cache reuse, caller-sensitive cache-key
separation, and reset invalidation through `module_resolve_uncached_count()`.
It also audits the retained profile for self-hosted provenance, bounded
execution, Rust/C/Go/Python/Bun parity, explicit native byte-fixture mode, and
exact 1/4/32 MiB byte checks. The Linux-only byte producer requires GNU
`/usr/bin/time` and `timeout`; a focused contract proves fast-exit RSS, known
child inclusion, and bounded timeout failure. Unsupported hosts are unavailable,
and no unbounded fallback is admitted. It rejects total process RSS above four
times payload and enforces the fixture's 1 MiB `<1000 ms` and 32 MiB `<30000 ms`
receipts while retaining separate host wall samples.

The gate opens a facade measurement generation and compares 100 cache-reset
misses with 1000 retained requests. It requires identical resolution, uncached
counts of 100 and 1, a positive baseline of **failed existence probes**, and a
90% reduction (`cached * 100 <= baseline * 10`). The packed result contains
total in high 31 bits and failed in low 32 bits; negative values are errors.
The shared invariant is `failed <= total <= 0x7fffffff`. A deterministic direct
facade check asserts exact `(total, failed) = (2, 2)` using a per-process path
that is required to be absent without deleting it.
Native providers admit a generation lease before the facade filesystem work,
clear accepting before drain, and use a 63-bit no-wrap token that fails closed
at overflow. The source gate does not claim disabled-path assembly or cycles.
It does not claim a timing benchmark, a filesystem syscall reduction, or a
Stage 4 admission.

The focused C selfcheck is separate from the Simple SSpec: it compiles and runs
the test-only counter-seed harness against both C providers. Its PID-scoped
fixture must already be absent and is never deleted.

## Provisional requirement mapping

The executable `@req` identifiers are provisional until the user selects the
feature and NFR option documents. The facade lifecycle and admission scenarios
cover REQ-001/003; cross-language equivalence and retained rows cover
REQ-001/002; cache reuse/reset/probe reduction cover REQ-004..REQ-007; and the
byte fixture plus packed-boundary audit cover REQ-008. NFR-001/002 cover
latency/cache effectiveness, NFR-003 packed storage and capability safety,
NFR-004 RSS/cross-language comparability, NFR-005 provenance, and NFR-006
fail-closed bounded evidence.

This mapping improves operator traceability but is not docgen provenance. The
manual stays blocked until an admitted generator records scenario sections,
source hash, and `0 stubs`, followed by a readability review.
