# Simple Compiler Performance and Memory Efficiency

Status: **executable source contract present; runtime execution blocked by the
missing admitted Stage-4 binary**.

## Purpose and audience

This operator-facing flow explains how compiler developers will verify truthful optimizer activation, shared analysis facts, actionable diagnostics, semantic preservation, and performance/resource budgets. It traces REQ-001 through REQ-025; focused integration and performance specs provide the detailed matrices.

## Preconditions

- An admitted self-hosted pure-Simple binary with path, hash, stage, provenance, and supported-command receipt.
- Fixed source/MIR/lint/profile fixtures and baseline receipts.
- No Rust seed, stub fallback, source-string oracle, or hand-authored success record.

## Primary flow

### 1. Load the effective optimizer pipeline

Inspect requested versus effective passes, status, expectation, backend delegation, disabled reasons, stable ordering, and machine output. Unknown passes or unavailable required facts must fail closed.

### 2. Reject dishonest active transforms

Run positive and negative witnesses, compiler integrity rules, candidate/transformed/rejected counters, vector containment, post-transform verification, and the applicable adversarial matrix.

### 3. Analyze one function with shared performance facts

Prove one CFG/predecessor/RPO construction per revision, cache reuse, targeted invalidation, conservative escape/COW behavior, bounded costs, CollectionPlan facts, and explicit incomplete outcomes.

### 4. Report actionable performance and memory diagnostics

Check stable rule identity, warning/error versus remark placement, exact spans, confidence/tier/cost, fix applicability, suppression, deterministic text/JSON, and legacy COLL compatibility.

### 5. Preserve semantics while applying a proven transform

Compare optimized and unoptimized behavior across results, exits, stdout/stderr, errors, allocation/COW counters, zero-trip, alias, effect/order, early-exit, and numeric semantics. Rejected candidates explain the exact blocker.

### 6. Compare compiler and runtime evidence against the baseline

Validate provenance and compare frontend reuse, Tier-0/Tier-1 time, RSS, analysis construction, warm tool requests, `.sperf`, `.sprof-v2`, and multi-size empirical curves. One timeout or unknown analysis never certifies complexity.

## Current limitation

The executable helper flow now invokes production pass-status, effective
pipeline, `PerfFacts`, diagnostic-evidence, and quarantined-transform APIs with
typed oracles. It is not PASS evidence until the admitted self-hosted binary is
restored and this exact spec plus docgen/maintenance gates execute. Runtime time
and RSS budgets remain separate performance evidence, not source assertions.

## Evidence policy

Primary steps stay visible. Setup and adversarial matrices fold once implemented. Rejection reasons, provenance, incomplete rows, and claim boundaries remain visible. Executable SSpec belongs under `test/`; no `.spl` file belongs under `doc/06_spec`.
