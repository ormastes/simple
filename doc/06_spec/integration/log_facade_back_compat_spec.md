# log_facade_back_compat_spec

> log-lib-drivers Phase 4 spec — back-compat for existing log call sites.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# log_facade_back_compat_spec

log-lib-drivers Phase 4 spec — back-compat for existing log call sites.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/log_facade_back_compat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

log-lib-drivers Phase 4 spec — back-compat for existing log call sites.

Covers AC-4 (back-compat: existing `log.info(...)` / `log.warn(...)`
call sites must keep working).

Status: RED PHASE. Phase 5 has not rerouted `nogc_sync_mut/log.spl`
through the new facade yet.

Phase 3 contract (locked, §F):
  - `use std.log.{error, warn, info, debug, fatal}` resolves; signatures
    `info(scope: text, msg: text)` etc. unchanged.
  - `nogc_sync_mut.log.spl` `_emit` rewritten to call
    `log_dispatch_text(canonical_level, subsys_from_scope(scope), bytes)`.
  - `subsys_from_scope("pkg")` -> SUBSYS_PKG, "cli" -> SUBSYS_CLI,
    "test" -> SUBSYS_TEST. Unknown scope -> SUBSYS_USER_BASE.
  - The duplicate `src/lib/nogc_sync_mut/src/log.spl` keeps working
    (marked DEPRECATED — Phase 6 deletes; this spec must NOT block on
    that decision).

## Scenarios

### log facade — top-level imports resolve (AC-4)

#### AC-4: `use std.log.{error, warn, info, debug}` resolves

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-4: `use std.log.{error, warn, info, debug}` resolves
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: `use std.log.{error, warn, info, debug}` resolves")
# Compile-time check: if these names don't resolve, the file
# doesn't compile — which is the failure signal in red phase.
expect(true).to_equal(true)
```

</details>

#### AC-4: log.info(scope, msg) emits without crashing

- AC-4: log.info(scope, msg) emits without crashing


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: log.info(scope, msg) emits without crashing")
log_set_level(LOG_TRACE)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
info("pkg", "package install starting")
warn("cli", "cli got a deprecation hit")
debug("test", "test runner spawned")
error("pkg", "package install failed")
expect(ring_backend_count(sink)).to_be_greater_than(3)
log_remove_backend(id)
```

</details>

### log facade — scope→subsys mapping (AC-4)

#### AC-4: subsys_from_scope routes legacy scopes to canonical IDs

- AC-4: subsys_from_scope routes legacy scopes to canonical IDs
   - Expected: subsys_from_scope("pkg") equals `SUBSYS_PKG`
   - Expected: subsys_from_scope("cli") equals `SUBSYS_CLI`
   - Expected: subsys_from_scope("test") equals `SUBSYS_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: subsys_from_scope routes legacy scopes to canonical IDs")
expect(subsys_from_scope("pkg")).to_equal(SUBSYS_PKG)
expect(subsys_from_scope("cli")).to_equal(SUBSYS_CLI)
expect(subsys_from_scope("test")).to_equal(SUBSYS_TEST)
```

</details>

#### AC-4: unknown scope falls through to SUBSYS_USER_BASE

- AC-4: unknown scope falls through to SUBSYS_USER_BASE
   - Expected: subsys_from_scope("not-a-known-scope") equals `SUBSYS_USER_BASE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: unknown scope falls through to SUBSYS_USER_BASE")
expect(subsys_from_scope("not-a-known-scope")).to_equal(SUBSYS_USER_BASE)
```

</details>

### log facade — legacy emission round-trips through facade (AC-4)

#### AC-4: legacy info('pkg', ...) lands as SUBSYS_PKG record

- AC-4: legacy info('pkg', ...) lands as SUBSYS_PKG record
   - Expected: ring_backend_count(sink) equals `1`
   - Expected: ring_backend_subsys_at(sink, 0) equals `SUBSYS_PKG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: legacy info('pkg', ...) lands as SUBSYS_PKG record")
log_set_level(LOG_TRACE)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
info("pkg", "hello")
expect(ring_backend_count(sink)).to_equal(1)
expect(ring_backend_subsys_at(sink, 0)).to_equal(SUBSYS_PKG)
log_remove_backend(id)
```

</details>

#### AC-4: legacy warn('cli', ...) lands as SUBSYS_CLI record

- AC-4: legacy warn('cli', ...) lands as SUBSYS_CLI record
   - Expected: ring_backend_subsys_at(sink, 0) equals `SUBSYS_CLI`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: legacy warn('cli', ...) lands as SUBSYS_CLI record")
log_set_level(LOG_TRACE)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
warn("cli", "hi from cli")
expect(ring_backend_subsys_at(sink, 0)).to_equal(SUBSYS_CLI)
log_remove_backend(id)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e5f69c2481fb91d3aea4cc4da2ea258134f704e517eb96efd28eda33322d6d76`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5f69c2481fb91d3aea4cc4da2ea258134f704e517eb96efd28eda33322d6d76`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5f69c2481fb91d3aea4cc4da2ea258134f704e517eb96efd28eda33322d6d76`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/log_facade_back_compat_spec.spl
mirror: doc/06_spec/integration/log_facade_back_compat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/log_facade_back_compat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/log_facade_back_compat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/log_facade_back_compat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/log_facade_back_compat_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: `use std.log.{error, warn, info, debug}` resolves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/log_facade_back_compat_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: log.info(scope, msg) emits without crashing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/log_facade_back_compat_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: subsys_from_scope routes legacy scopes to canonical IDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
