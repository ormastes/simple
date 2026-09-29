# audit_log_hash_chain_spec

> Purpose: Verify audit chain — genesis & append (AC-5, AC-6e).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# audit_log_hash_chain_spec

Purpose: Verify audit chain — genesis & append (AC-5, AC-6e).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/audit_log_hash_chain_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify audit chain — genesis & append (AC-5, AC-6e).
Audience: compiler and tooling engineers who maintain this spec.

log-lib-drivers Phase 4 spec — audit-log tamper-evident hash chain.

Covers AC-5 (audit-log uses tamper-evident framing — sequence + hash
chain) and AC-6e (audit-log tamper-evident behavior).

Status: RED PHASE. Phase 5 has not implemented audit_chain.spl yet.

Phase 3 contract (locked, §E):
  AuditEntry NEW fields (additive):
    seq:         u64       (monotonic, 1-based; genesis seq=1)
    prev_hash:   [u8; 32]  (genesis = [0u8; 32])
    entry_hash:  [u8; 32]  (sha256 of canonical input)

  Canonical hash input (deterministic, must match verifier):
    hash_input = u64_be(seq)
              || u64_be(timestamp_ms)
              || u8(severity_rank)
              || event_json_bytes
              || prev_hash
    entry_hash = sha256(hash_input)

  audit_chain_init(file_path, fsync_each)
    - Genesis: next_seq = 1, last_hash = [0u8; 32]
    - Recovery: read LAST line only (O(1)); set last_hash, next_seq.

  audit_chain_append(entry, config) — fills seq/prev_hash/entry_hash.
  audit_chain_verify(file_path) -> Result<u64, AuditError>
    - Err(ChainBreakAt(seq)) on tamper / hash mismatch.
    - AuditError variants: Io(text), BadJson(u64), ChainBreakAt(u64),
                            SeqGapAt(u64), HashMismatchAt(u64).

  Severity ordering preserved — `meets_severity` callers must continue
  to compile and behave identically.

## Scenarios

### audit chain — genesis & append (AC-5, AC-6e)

#### AC-5: genesis entry has seq=1 and prev_hash=[0u8;32]

- Verify: AC-5: genesis entry has seq=1 and prev_hash=[0u8;32]
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-5: genesis entry has seq=1 and prev_hash=[0u8;32]")
# @req: REQ-LIB-AUDIT-LOG-HASH-001
# Fresh file → genesis state.
remove_file_if_exists(TMP_AUDIT_PATH)
audit_chain_init(TMP_AUDIT_PATH, false)
val cfg = AuditConfig(
    enabled: true,
    min_severity: SecuritySeverity.Info,
    log_to_stdout: false,
    log_file: TMP_AUDIT_PATH,
    mask_secrets: false
)
val entry = AuditEntry.new(
    event: SecurityEvent.AuthSuccess(user: "alice", peer: "127.0.0.1"),
    correlation_id: "corr-1",
    module_path: "test"
)
audit_chain_append(entry, cfg)
# Verify the produced file: 1 valid entry.
val result = audit_chain_verify(TMP_AUDIT_PATH)
expect(result).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### AC-5: three appended entries verify clean

- Verify: AC-5: three appended entries verify clean
   - Expected: audit_chain_verify(TMP_AUDIT_PATH) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-5: three appended entries verify clean")
remove_file_if_exists(TMP_AUDIT_PATH)
audit_chain_init(TMP_AUDIT_PATH, false)
val cfg = AuditConfig(
    enabled: true,
    min_severity: SecuritySeverity.Info,
    log_to_stdout: false,
    log_file: TMP_AUDIT_PATH,
    mask_secrets: false
)
var i = 0
while i < 3:
    val e = AuditEntry.new(
        event: SecurityEvent.AuthSuccess(user: "u", peer: "p"),
        correlation_id: "corr",
        module_path: "test"
    )
    audit_chain_append(e, cfg)
    i = i + 1
expect(audit_chain_verify(TMP_AUDIT_PATH)).to_equal(3)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### AC-5: each entry_hash equals sha256(seq_be||ts_be||sev||json||prev_hash)

- Verify: AC-5: each entry_hash equals sha256(seq_be||ts_be||sev||json||prev_hash)
   - Expected: e.seq equals `1`
   - Expected: audit_chain_is_zero_hash(e.prev_hash) is true
   - Expected: audit_chain_hashes_equal(e.entry_hash, recomputed) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-5: each entry_hash equals sha256(seq_be||ts_be||sev||json||prev_hash)")
# Phase 5 exposes audit_chain_recompute_hash(entry) for testing.
remove_file_if_exists(TMP_AUDIT_PATH)
audit_chain_init(TMP_AUDIT_PATH, false)
val cfg = AuditConfig(
    enabled: true,
    min_severity: SecuritySeverity.Info,
    log_to_stdout: false,
    log_file: TMP_AUDIT_PATH,
    mask_secrets: false
)
val e = AuditEntry.new(
    event: SecurityEvent.AuthSuccess(user: "u", peer: "p"),
    correlation_id: "c",
    module_path: "m"
)
audit_chain_append(e, cfg)
# After append, e.seq, e.prev_hash, e.entry_hash are populated.
expect(e.seq).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
# prev_hash must be the genesis zero hash.
expect(audit_chain_is_zero_hash(e.prev_hash)).to_equal(true)
# entry_hash recomputes deterministically.
val recomputed = audit_chain_recompute_hash(e)
expect(audit_chain_hashes_equal(e.entry_hash, recomputed)).to_equal(true)
```

</details>

### audit chain — tamper detection (AC-5, AC-6e)

#### AC-6e: flipping a byte in middle entry returns Err(ChainBreakAt(2))

- Verify: AC-6e: flipping a byte in middle entry returns Err(ChainBreakAt(2))
   - Expected: audit_chain_error_is_chain_break_at(result, 2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-6e: flipping a byte in middle entry returns Err(ChainBreakAt(2))")
# Append 3 entries, then corrupt entry #2 (1-based seq).
remove_file_if_exists(TMP_AUDIT_PATH)
audit_chain_init(TMP_AUDIT_PATH, false)
val cfg = AuditConfig(
    enabled: true,
    min_severity: SecuritySeverity.Info,
    log_to_stdout: false,
    log_file: TMP_AUDIT_PATH,
    mask_secrets: false
)
var i = 0
while i < 3:
    val e = AuditEntry.new(
        event: SecurityEvent.AuthSuccess(user: "u", peer: "p"),
        correlation_id: "c",
        module_path: "m"
    )
    audit_chain_append(e, cfg)
    i = i + 1
# Tamper: flip a byte in line 2 (the middle entry).
# Phase 5 helper: audit_chain_test_tamper_byte(path, line_index_1based, byte_offset_in_line).
audit_chain_test_tamper_byte(TMP_AUDIT_PATH, 2, 10)
# Verify must report ChainBreakAt(2) — Phase-3 §E names: positional, not record syntax.
val result = audit_chain_verify(TMP_AUDIT_PATH)
expect(audit_chain_error_is_chain_break_at(result, 2)).to_equal(true)
```

</details>

### audit chain — recovery (AC-5)

#### AC-5: opening existing chain reads only last line for prev_hash

- Verify: AC-5: opening existing chain reads only last line for prev_hash
   - Expected: e3.seq equals `3`
   - Expected: audit_chain_verify(TMP_AUDIT_PATH) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-5: opening existing chain reads only last line for prev_hash")
# Pre-seed the file with 2 entries.
remove_file_if_exists(TMP_AUDIT_PATH)
audit_chain_init(TMP_AUDIT_PATH, false)
val cfg = AuditConfig(
    enabled: true,
    min_severity: SecuritySeverity.Info,
    log_to_stdout: false,
    log_file: TMP_AUDIT_PATH,
    mask_secrets: false
)
var i = 0
while i < 2:
    val e = AuditEntry.new(
        event: SecurityEvent.AuthSuccess(user: "u", peer: "p"),
        correlation_id: "c",
        module_path: "m"
    )
    audit_chain_append(e, cfg)
    i = i + 1
# Re-init: should pick up next_seq=3 from last-line scan, NOT replay all.
audit_chain_init(TMP_AUDIT_PATH, false)
val e3 = AuditEntry.new(
    event: SecurityEvent.AuthSuccess(user: "u", peer: "p"),
    correlation_id: "c",
    module_path: "m"
)
audit_chain_append(e3, cfg)
expect(e3.seq).to_equal(3)  # oracle: authoritative expected value documented by this spec's contract
# Full chain still verifies after recovery+append.
expect(audit_chain_verify(TMP_AUDIT_PATH)).to_equal(3)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### audit chain — back-compat with severity (AC-5)

#### AC-5: meets_severity ordering preserved (Info < Warning < Critical)

- Verify: AC-5: meets_severity ordering preserved (Info < Warning < Critical)
   - Expected: meets_severity(SecuritySeverity.Info, SecuritySeverity.Info) is true
   - Expected: meets_severity(SecuritySeverity.Warning, SecuritySeverity.Info) is true
   - Expected: meets_severity(SecuritySeverity.Critical, SecuritySeverity.Warning) is true
   - Expected: meets_severity(SecuritySeverity.Info, SecuritySeverity.Warning) is false
   - Expected: meets_severity(SecuritySeverity.Info, SecuritySeverity.Critical) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-5: meets_severity ordering preserved (Info < Warning < Critical)")
# Phase-3 contract: existing severity ranks are unchanged.
expect(meets_severity(SecuritySeverity.Info, SecuritySeverity.Info)).to_equal(true)
expect(meets_severity(SecuritySeverity.Warning, SecuritySeverity.Info)).to_equal(true)
expect(meets_severity(SecuritySeverity.Critical, SecuritySeverity.Warning)).to_equal(true)
expect(meets_severity(SecuritySeverity.Info, SecuritySeverity.Warning)).to_equal(false)
expect(meets_severity(SecuritySeverity.Info, SecuritySeverity.Critical)).to_equal(false)
```

</details>

#### AC-5: severity_for_event mapping unchanged

- Verify: AC-5: severity_for_event mapping unchanged
   - Expected: s equals `SecuritySeverity.Critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: AC-5: severity_for_event mapping unchanged")
val s = severity_for_event(SecurityEvent.CsrfViolation(peer: "127.0.0.1", path: "/admin"))
expect(s).to_equal(SecuritySeverity.Critical)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-LIB-AUDIT-LOG-HASH-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `20d51dcbd982a9a406b986516fb81a4ff314016f664fe5e2a3bf0f09f5a6b5bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20d51dcbd982a9a406b986516fb81a4ff314016f664fe5e2a3bf0f09f5a6b5bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20d51dcbd982a9a406b986516fb81a4ff314016f664fe5e2a3bf0f09f5a6b5bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/audit_log_hash_chain_spec.spl
mirror: doc/06_spec/unit/lib/audit_log_hash_chain_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/audit_log_hash_chain_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/audit_log_hash_chain_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/audit_log_hash_chain_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/lib/audit_log_hash_chain_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/unit/lib/audit_log_hash_chain_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: genesis entry has seq=1 and prev_hash=[0u8;32]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/audit_log_hash_chain_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: three appended entries verify clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/audit_log_hash_chain_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: each entry_hash equals sha256(seq_be||ts_be||sev||json||prev_hash)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
