<!-- codex-design: Astra, 2026-09-27 -->
# Frontend Advisory Execution Authority V1 — Focused Test Plan

**Status: planned; no execution or performance PASS.**

Extends [the parent test plan](environment_optimized_dynamic_libraries.md) and
[the authority design](../../05_design/compiler/frontend_advisory_execution_authority_v1.md).
The parent plan is concurrently owned by the inspector lane and is unchanged.
These are Stage 3/E3 acceptance subcases, not new weighted ledger rows. Existing
fail-fast system scenarios and the pending E1–E5 evidence totals remain intact.

## Production entry and fixtures

Drive `parse_full_frontend_selected_v1` through the actual post-transform
frontend seam. A positive native fixture must construct a genuinely admitted
sealed activation and lexical package on a compatible execution domain. Neither
mocked execution flags, forged result structs nor source-text assertions can
close a positive execution gate. Name runner path/hash/admission, target ABI,
CPU/OS-usable features, provider bytes, environment generation and exact commands.
Unsupported hosts remain blocked; QEMU receipts do not claim physical speedup.

Extend the existing executable system spec under
`test/03_system/app/compiler/feature/environment_optimized_dynamic_libraries_spec.spl`
only when its real owner-backed setup exists. Keep the frozen helper names
`setup_environment_catalog`, `step_admit_variant`, `step_bind_provider` and
`check_execution_receipt`. No placeholder implementation is added by this plan.

## Falsifiable scenario matrix

| Subcase | Requirements | Required observation |
|---|---|---|
| Actual invocation | REQ-004/008/009/014 | Prefer and Require reach guarded native calls on admitted input of at least 32 bytes; masks equal scalar oracle; positive invocation count and exact terminal proof precede reference parser admission |
| Independent request | REQ-003/006/014 | Change returned source digest/length, lexical state or transformed source while preserving a self-consistent receipt: consumption rejects |
| Sealed join | REQ-003/004/012 | Wrong package/provider/artifact/interface/ABI/environment generation or revoked activation fails before native invocation |
| Token lifecycle | REQ-006/012/014 | Wrong owner, forged coordinates, duplicate consumption, retired startup session and reused record slot reject; no public receipt constructor authorizes dispatch |
| Nonce issuance | NFR-001/007 | Checked `random_hex(16)` yields one nonce per operation; injected `nil`, malformed/all-zero raw entropy, and retained-record collision fail without token/session creation; cleanup retry preserves the nonce |
| Source snapshot identity | REQ-003/008/012 | Owner-minted nonzero `u64` binds full transformed-source digest/length; counter zero/exhaustion/collision reject before session creation; append/reset never reuses an identity, including equal-byte snapshots |
| Resource failures | REQ-005/012 | Inject preparation, native-call, oracle, operation-close, session-close and build-use-release failures independently; retain pending resources, retry exact cleanup, never issue Ready early |
| Policy distinction | REQ-005/008 | Prefer discards partial masks before truthful fallback; Require returns error before cache/parser admission; tiny input follows the documented no-complete-block rule |
| Session isolation | REQ-008/012 | Reset/append/new-file transformed snapshots obtain distinct source sessions; no source/lexical state leaks after failure or reuse |
| Semantic parity | REQ-008/009 | Provider on/off yields identical normalized AST/HIR, diagnostics/order/spans, domain blocks, interpolation and placeholders, including malformed and Unicode input |
| Cache/revocation | REQ-006/012/014 | Hits still require current token consumption; stale-generation keys miss; fallback cannot inherit executed provenance; unavailable canonical cache join disables selected reuse |
| Bounds/cancellation | NFR-001/007 | Exact/max-plus-one source and record limits; 64 Ready/quarantined records enforce capacity; cancellation drains or quarantines; no token-ID wrap or history-based replay |
| Lazy startup | REQ-013; NFR-009 | Reference/help/version invoke no provider, initialize no GPU, and preserve baseline startup/cache behavior |

Unit extensions belong beside
`test/01_unit/compiler/loader/frontend_lexical_advisory_adapter_v1_spec.spl`,
`frontend_lexical_advisory_result_validation_v1_spec.spl`, and
`test/01_unit/compiler/frontend/environment_variant_frontend_policy_binding_v1_spec.spl`.
Add the proposed owner unit spec at
`test/01_unit/compiler/loader/frontend_advisory_execution_owner_v1_spec.spl`.
Pure state-transition fixtures must be labeled as such; they cannot substitute
for production native invocation and lifetime evidence.

## Latency and retained evidence

Fixture corpus: lengths 0–65, medium 64 KiB, large 1 MiB, Unicode-heavy input,
malformed recovery, transformed domain/interpolation cases, and incremental
append/reset. Include every SIMD tail length and same-source warm-cache cases.
Collect cold/warm p50/p95/p99 and max RSS; split source digest, owner issue,
session creation, native/oracle work, cleanup, consume, cache and full parse.
Include all costs in end-to-end totals. Native invocation and output digests
must correlate with the same provider/environment/request as timing samples.

Retain the selected thresholds: selection p95 ≤1 ms warm/25 ms cold; dispatch
overhead ≤2% without per-element lifecycle work; speedup ≥1.15x on a declared
same-machine workload; selected RSS increase ≤5%, unselected overhead ≤2 MiB.
Report unachieved thresholds honestly and keep promotion closed. Run each gate
once for an unchanged revision, cap verify/fix cycles at three, and retain exact
base/head, commands, terminal results and reviewer disposition.
