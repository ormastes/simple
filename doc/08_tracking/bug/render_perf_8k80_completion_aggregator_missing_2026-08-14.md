## Triage 2026-08-17 — BLOCKED, skipped fast (not a compiler/runtime/tooling defect)

Blocker: unchanged and self-declared in this doc — the A7 aggregator is
IMPLEMENTED (`scripts/check/check-render-perf-8k80-container.shs`); what is
missing is live native A4 (CPU DrawIR) and A5 (strict Vulkan) receipts for the
same 7680x4320 workload. Requires the NVIDIA CUDA/Vulkan container host. Nothing
to fix in source.
# Render performance 8K80 parent aggregator is missing

Status: **IMPLEMENTED / LIVE EVIDENCE BLOCKED**

The canonical plan's A7 row requires one parent-authoritative decision over
the production-native CPU DrawIR receipt, strict Vulkan semantic-producer
receipt, and optional physical-presentation receipt. No
The `scripts/check/check-render-perf-8k80-container.shs` owner now exists; its
bounded positive and deliberate-red contract test passes. Live correlation is
still blocked by the admitted native A4/A5 artifacts, so
separate green rows could otherwise be combined manually or promoted despite
mismatched viewport, damage class, revision, device, or artifact provenance.

## Location and effect

- Plan contract: `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md`,
  A7 in §0-B.
- Research/design: `doc/01_research/local/render_8k80_container_gpu_completion.md`
  and `doc/04_architecture/render_8k80_container_gpu_completion.md`.
- Canonical Todo owner: TODO811.
- Implementation: `scripts/check/check-render-perf-8k80-container.shs`.
- Blocked acceptance: A7 and umbrella 8K80 promotion.

## Unblock condition

Run the implemented wrapper with explicit DrawIR, producer, optional physical,
and report inputs. It must correlate the CPU-native A4 and strict Vulkan A5
receipts for the same 7680x4320 workload, damage class, revision, and artifact
provenance; require p95 at most 12.5 ms, nonzero RSS/checksum, exact readback
scope, no disallowed fallback, and known completion; and reject missing,
duplicate, unknown, stale, or mismatched fields. A valid A4+A5 result without
physical evidence publishes `blocked-physical`. Only a fresh correlated
TODO684/TODO685 receipt can promote full PASS.

The bounded self-test matrix specified by TODO811 includes software-only
`blocked-physical`, physical promotion, and deliberate-red malformed,
mismatched, fallback, unknown-completion, zero-metric, timed-readback, and
over-budget rows.

Retain the generated aggregate plus every correlated input receipt. Owner:
render-performance integration. Final reviewer: independent highest-capability
Codex.
