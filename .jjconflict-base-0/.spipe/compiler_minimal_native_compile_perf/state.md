# Feature: compiler_minimal_native_compile_perf

## Goal

Provide a disjoint, fail-closed minimal native-compile benchmark with exact
pure-Simple provenance, non-vacuous artifact checks, and fixed time/RSS gates.

## Acceptance state

- AC-1 implementation and pure decision contracts: COMPLETE in source.
- AC-2 modern step-based SSpec with real assertions and REQ traceability:
  COMPLETE in source; live execution TEST_BLOCKED.
- AC-3 mirrored Markdown manual, test plan, guide, and lane expert knowledge:
  COMPLETE; docgen provenance TEST_BLOCKED.
- AC-4 admitted measured baseline and current five-sample result: TEST_BLOCKED.
- AC-5 runtime verification PASS: TEST_BLOCKED and not claimed.

## Runtime blocker

`TEST_BLOCKED`: the prepared future-executable SSpec has not run under a
qualified pure-Simple full CLI. Static/source-contract guards are not runtime
PASS evidence.

As of 2026-08-16 no admitted pure-Simple full CLI is runnable in this isolated
worktree. The available admitted Stage2 artifact (SHA-256
`68cbbbbd60ed073e2e21aac682207f0c21cef703f5fe7a920fee3e32c19af2aa`)
supports only compile/native-build and failed three distinct minimal probes
with exit 70 before output, reporting `str.clear was called on a receiver that
is not text`. The unreceipted release CLI segfaults, and Rust seeds are excluded.

## Resume contract

Once an admitted full CLI and an admitted compiler/baseline tuple exist, export
the variables in the system test plan and run its single focused command once.
Retain the stdout, exact environment tuple, and admission receipt. Stop after a
PASS or after three total verify/fix cycles; never repeat an unchanged command.

## Phase

dev — implementation complete, runtime evidence TEST_BLOCKED

## Review scope

Cooperative sidecar review is N/A for this narrow lane-owned benchmark capsule.
The final verifier owns SSpec/manual/guide/wiki consistency and must preserve
the runtime `TEST_BLOCKED` claim until qualified execution exists.
