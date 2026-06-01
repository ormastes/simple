<!-- codex-requirements -->
# NFR Requirements: Harden TUI/GUI Layout Comparison

Selected option: NFR Option C, Backend-Qualified Acceleration Gate.

## Requirements

NFR-001: Focused comparison correctness specs must pass uncached after changes to comparison, capture, corpus, or backend evidence code.

NFR-002: Changed executable specs and touched comparison/backend implementation files must contain no placeholder passes, `pass_todo`, false-pass assertions, or TODO-only behavior.

NFR-003: The `doc/06_spec` tree must contain zero executable `.spl` spec files before verify/release.

NFR-004: Generated/manual scenario docs for changed specs must explain the acceptance policy, failure modes, and evidence purpose well enough to review without opening the executable spec.

NFR-005: Warm startup timing, max RSS, and binary-size deltas must be measured for representative comparison/backend CLI targets before claiming size or performance improvement.

NFR-006: Metal, Vulkan, CUDA, and CPU SIMD lanes must each produce a backend-qualified evidence record with initialized, unavailable, failed, or fallback status.

NFR-007: Initialized accelerated lanes must be compared against scalar/software baseline output before any optimization claim is accepted.

NFR-008: Backend timing evidence must record command, host, backend, warmup count, sample count, p50, p95, and render/readback scope for each initialized lane.

NFR-009: Hardware/runtime absence is acceptable in this development environment only when recorded as explicit unavailable evidence or tracked follow-up, not when hidden by fallback success.

NFR-010: The verification report for this feature must state which backend lanes were proven on the current host and which lanes remain unavailable or externally blocked.

## Current Evidence

- Correctness gates currently pass for backend screenshot comparison, HTML compatibility comparison, emulated capture, famous-site corpus pair comparison, and strict backend probe coverage.
- Backend status evidence exists for Metal, Vulkan, CUDA, and CPU SIMD lanes.
- Full timing, RSS, binary-size delta, and initialized accelerated-lane correctness evidence remains to be implemented before final verify can claim NFR-005 through NFR-010 complete.
