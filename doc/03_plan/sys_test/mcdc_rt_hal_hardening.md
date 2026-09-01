# System Test Plan: MC/DC, RT, and HAL Hardening

## Suites

Create executable specs and exact mirrored manuals for:

1. `coverage/mcdc_modes_and_semantics_spec.spl` — REQ-001/002/003/007/014.
2. `coverage/mcdc_enforcement_and_exclusions_spec.spl` — REQ-005/006/015.
3. `coverage/mcdc_parallel_recording_spec.spl` — REQ-004/014.
4. `coverage/mcdc_perf_memory_contract_spec.spl` — NFR-001..010.
5. `runtime/rt_hal_provider_differential_spec.spl` — REQ-008/009/014.
6. `runtime/rt_hal_environment_receipt_spec.spl` — REQ-010/011.
7. `runtime/rt_criticality_hardening_spec.spl` — REQ-012/013/015.
8. `runtime/rt_hal_external_provider_protocol_spec.spl` — supporting REQ-008/009/010/014 typed C/Rust tool-admission and provider-identity protocol coverage.

Each REQ has happy, boundary, and failure scenarios. Built-in matchers inspect
concrete production records; unfinished oracles call `fail(...)`. Setup is hidden
with `@inline`; primary manuals show the shared `step("...")` flows. Environment
and perf scenarios capture typed exec/artifact receipts; source strings and
screenshots alone are not evidence.

## Required evidence

Static-off IR/native inventory, truth/evaluation traces, exact pairs/exclusions,
interpreter/native identity, deterministic parallel bytes, bounded saturation,
provider effects, environment receipts, staged diagnostics, optimizer receipt,
same-fixture timing/RSS/allocation receipts, and exact basis-point boundaries.

Only the pure-Simple self-hosted runtime is admitted. BLOCKED retains reason,
prerequisite, owner, artifact paths and resume command and cannot satisfy a gate.
Each acceptance criterion is run at most once per session.

## Current implementation mapping (unverified)

The seven primary system specs and their mirrored Markdown manuals now exist.
The external-provider protocol suite is supporting evidence and must also retain
its mirrored Markdown manual. It validates typed admission and identity pinning;
the differential suite remains the owner of result/effect parity behavior.
Additional focused unit specs cover compile options, HIR/MIR control lowering,
probe protocol and dynamic lifecycle, masking analysis, runner transport/gate,
reasoned omissions, environment-plan validation, exact RT/HAL process arena,
tag retention, RT criticality, and recoverable unwind. Presence and generated
manual text are not PASS evidence.

The performance harness under `test/05_perf/mcdc_rt_hal/` contains:

1. `mcdc_decision_fixture.spl` for identical off/static/dynamic decision loops
   with cold setup outside the measured interval.
2. `mcdc_analyzer_fixture.spl` for evaluation/condition scaling.
3. `rt_hal_fixture.spl` for Pure-authoritative comparison work.
4. `thresholds.sdn`, `optimizer_inputs.txt`, `run_optimizer_receipts.shs`, and
   `run_perf_evidence.shs` for pinned integer-threshold receipts.

The acceptance run must execute each still-red criterion once using an admitted
self-hosted runtime. It must attach static-off MIR/native inventory; static-on
and dormant/enabled timing, peak RSS, and allocation evidence from the same
fixture; analyzer scaling; deterministic output; optimizer receipts; runner
exit status; and exact RT/HAL/env receipts. V3 is compiler-staged and
identity-sealed; public V2 and direct V3 installation must reject before
partial host setup. It must also exercise supported
unwind targets and confirm stable rejection on C, LLVM-library, RV32, Mach-O,
and other unsupported targets. Current status: **UNVERIFIED** because Stage 3/4
has not produced an admitted executable.

## Remediation coverage additions (unverified)

The eventual single acceptance run must cover formal contexts for nested
`and`/`or`, short-circuit unknowns, repeated/coupled occurrences, fingerprint
mismatch, conflicting evidence, malformed postfix programs, the exact
64-requirement boundary, and rejection above it. Measure derivation as a cold
reporting cost separately from probe overhead.

Exercise the fixed RT receipt ring at empty, one row, 64 rows, saturation, owner
collision, cold drain, mismatch/timeout/cancel, and finalization with undrained
data. Hot-path evidence must show no allocation, hashing, process work,
formatting, or waiting; process/RSS evidence belongs to the cold drain.

Exercise all 24 environment instruction kinds. For physical operations,
exercise hardware-probe registration success, duplicate, 64-adapter cap, sealed
registry, undeclared ID, schema mismatch, narrower adapter bounds, unavailable
platform, truncation, and typed resume data. For socket/device/MMIO/IRQ/DMA
rows, retain a physical-or-blocked receipt with the same plan identity and exact
resume command. Confirm the adapter interface has no process-execution
capability.

Build and run both real external comparators only through the typed pinned plan,
verify output hashes before admission, compare the same Pure receipts, and
inject malformed/mismatched child output. Run unwind on supported POSIX ELF
targets and separately assert stable rejection for C, LLVM-library, Mach-O,
RV32, and other unsupported targets. None is currently accepted as PASS.
