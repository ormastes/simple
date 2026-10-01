# KPF Lifecycle Crash and Placement Parity

**Requirement:** REQ-KPF-007  
**Scope:** crash-loop policy and static/native/worker/optional-Wasm lifecycle parity

## Implementation

- `KpfLifecycleSupervisorV1` is the single mutable lifecycle owner.
- Restart timestamps are allocated to the declared maximum at construction;
  fault handling cannot grow the window.
- Fault state is generation scoped. Stale generations cannot consume a budget,
  restart, publish, or clear quarantine state.
- Exhaustion disables and quarantines only the failing provider generation.
  Every receipt records `host_failed: false`; a separately owned sibling remains
  published.
- Static, native, worker, and optional Wasm fixtures execute the same ordered
  prepare/start/publish/drain/retire/unload contract and emit equal receipt
  sequences.

## Verification

The focused SPipe scenario covers lifecycle parity, restart-window exhaustion,
provider-local containment, stale-generation rejection, replacement-generation
reset, deterministic receipts, and mutations for restart-budget bypass and
stale generation acceptance.

- Runtime: `/Users/ormastes/simple/bin/release/macos-arm64/simple`
- Runtime SHA-256: `277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767`
- Mode: interpreter
- Result: **4 passed, 0 failed**
