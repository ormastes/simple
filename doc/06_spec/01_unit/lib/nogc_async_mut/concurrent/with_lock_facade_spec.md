# Async-tier guard facade spec (SF4)

> Proves the nogc_async_mut mutex/rwlock facades re-export the guard-pattern

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async-tier guard facade spec (SF4)

Proves the nogc_async_mut mutex/rwlock facades re-export the guard-pattern

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent/with_lock_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the nogc_async_mut mutex/rwlock facades re-export the guard-pattern
API. Facade is sync-backed (blocks the carrier thread, no async suspend) —
see doc/08_tracking/bug/async_mutex_blocks_carrier_thread_no_suspend_2026-07-28.md

## Scenarios

### async-tier facade re-exports the guard API

#### mutex with_lock resolves through the facade and guards

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- mutex with_lock resolves through the facade and guards
   - Expected: mutex_with_lock(m, \v: v + 1) equals `2`
   - Expected: mutex_with_lock(m, \v: v) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mutex with_lock resolves through the facade and guards")
val m = mutex_new(1)
expect(mutex_with_lock(m, \v: v + 1)).to_equal(2)
expect(mutex_with_lock(m, \v: v)).to_equal(2)
```

</details>

#### rwlock with_write/with_read resolve through the facade

- rwlock with_write/with_read resolve through the facade
   - Expected: rwlock_with_write(rw, \v: v * 2) equals `8`
   - Expected: rwlock_with_read(rw, \v: v) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rwlock with_write/with_read resolve through the facade")
val rw = rwlock_new(4)
expect(rwlock_with_write(rw, \v: v * 2)).to_equal(8)
expect(rwlock_with_read(rw, \v: v)).to_equal(8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0a57925165bfda67135bfe9db5719f0cc42e716bf7e32e26ce15f20a6bcf050f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a57925165bfda67135bfe9db5719f0cc42e716bf7e32e26ce15f20a6bcf050f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a57925165bfda67135bfe9db5719f0cc42e716bf7e32e26ce15f20a6bcf050f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/concurrent/with_lock_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/with_lock_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/with_lock_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent/with_lock_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/concurrent/with_lock_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/concurrent/with_lock_facade_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mutex with_lock resolves through the facade and guards' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/concurrent/with_lock_facade_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rwlock with_write/with_read resolve through the facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
