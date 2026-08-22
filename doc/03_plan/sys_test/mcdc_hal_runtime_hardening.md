<!-- codex-design -->
# System Test Plan: MC/DC and HAL Runtime Hardening

## Executable spec split

1. `test/03_system/compiler/mcdc_instrumentation_modes_spec.spl` — REQ-001, 002, 006-008; NFR-001-006.
2. `test/03_system/compiler/mcdc_report_gate_spec.spl` — REQ-003-005, 018; NFR-008-009.
3. `test/03_system/runtime/hal_provider_comparison_spec.spl` — REQ-009-015; NFR-007, 010.
4. `test/03_system/runtime/hal_environment_replay_spec.spl` — REQ-015-018; NFR-005-010.
5. `test/03_system/runtime/hal_mission_critical_policy_spec.spl` — REQ-010-012, 019; NFR-005-006, 009.

## Manual flow vocabulary

Primary steps: “Build the controlled fixture”; “Run the selected assurance mode”; “Capture the durable receipt”; “Compare the bounded oracle”; “Inject one contract violation”; “Verify fail-closed evidence”. Setup helpers use `@inline`; matrix and sabotage sections are folded. Captures are `binary`, `protocol`, `log`, and `artifact`, never screenshots or source-string searches.

## Requirement coverage

- REQ-001/002: stable manifest and exact short-circuit vectors across interpreter/JIT/native; duplicate-ID and dropped-atom sabotage.
- REQ-003/004/005: unique-cause, valid/invalid masking, accounting equation, empty denominator, 99.99 failure, provenance tamper.
- REQ-006/007/008: static-off normalized code/symbol/section equivalence; static direct probes; lazy dynamic lifecycle; pack/overflow/load sabotage.
- REQ-009/010/011/012: complete declaration, critical default, lower-reachable rejection, caller storage, exact capacity, zero allocations on every exit path.
- REQ-013/014: process isolation, deterministic arrival-independent commit, child crash/hang/divergence, alpha/beta/normal and safe no-config default.
- REQ-015/016/017: I/O operation matrix, plan extraction/replay, malformed/missing/extra/reordered/duplicate/unsafe/timeout/overflow failures.
- REQ-018: every allowed exclusion class plus blank/generic/stale/forged/locally-producible rejection.
- REQ-019: new/changed error, exact legacy warning, moved/stale baseline error, milestone transition, shim absence.

## NFR evidence

Matched builds retain normalized hot code, symbols, sections, link maps, >=30 randomized paired samples, nearest-rank p95, CPU affinity/noise metadata, RSS, allocation epochs, mappings, raw sample hashes, capacities, log/event high-water, child receipts, and isolation setup/IPC metrics. Any missing identity/raw sample/child, NaN, overflow, evidence loss, or post-seal allocation fails.

## IRQ/MMIO/DMA device-adapter evidence

The focused contract spec
`test/01_unit/lib/common/structural/environment_device_adapter_spec.spl`
must prove exact capability/grant binding; MMIO range, width, alignment, access,
side-effect, and read-once rejection; ordered caller-buffer DMA map/submit/poll;
exact replay with no second model interaction; and rejection of blank or stale
hardware exclusions. A passing software-model scenario is not physical-device
evidence. Real-board rows remain unavailable unless an environment owner can
produce them safely; only a validated reason-bearing exclusion may remove such
a row from the MC/DC denominator.

The bounded executable gate is
`scripts/check/check-mcdc-performance-gate.shs`; its operator contract and
retained evidence fields are documented at
`doc/06_spec/05_perf/mcdc/mcdc_performance_gate_spec.md`. The gate records only
measurements it actually runs and exits with `ERROR nothing-checked` when an
input binary, compiler identity, tool, or receipt field is absent.

## Evidence rows

Current Linux host must cover compiler manifests, supported execution modes, three policies, dynload mappings, isolated Pure/C/Rust workers, allocation/performance receipts, and producible file/stream/process/env/clock/random/socket interactions. Real interrupt/MMIO/DMA and non-current platforms retain explicit target/executor identities and governed exclusion or blocked receipts; none count as PASS.

## Sabotage requirement

Each spec must prove green -> implementation sabotage red -> restored green. Arms target implementation: manifest IDs, probe emission, allocator call, slot publication, receipt validation, instruction order, provider isolation, comparison, and exclusion validation.
