# audit_log_hash_chain_spec

> log-lib-drivers Phase 4 spec — audit-log tamper-evident hash chain.

<!-- sdn-diagram:id=audit_log_hash_chain_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=audit_log_hash_chain_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

audit_log_hash_chain_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=audit_log_hash_chain_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# audit_log_hash_chain_spec

log-lib-drivers Phase 4 spec — audit-log tamper-evident hash chain.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/audit_log_hash_chain_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

1. std io runtime remove file if exists
2. audit chain init
3. event: SecurityEvent AuthSuccess
4. audit chain append
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Fresh file → genesis state.
std.io_runtime.remove_file_if_exists(TMP_AUDIT_PATH)
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
expect(result).to_equal(1)
```

</details>

#### AC-5: three appended entries verify clean

1. std io runtime remove file if exists
2. audit chain init
3. event: SecurityEvent AuthSuccess
4. audit chain append
   - Expected: audit_chain_verify(TMP_AUDIT_PATH) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
std.io_runtime.remove_file_if_exists(TMP_AUDIT_PATH)
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
expect(audit_chain_verify(TMP_AUDIT_PATH)).to_equal(3)
```

</details>

#### AC-5: each entry_hash equals sha256(seq_be||ts_be||sev||json||prev_hash)

1. std io runtime remove file if exists
2. audit chain init
3. event: SecurityEvent AuthSuccess
4. audit chain append
   - Expected: e.seq equals `1`
   - Expected: audit_chain_is_zero_hash(e.prev_hash) is true
   - Expected: audit_chain_hashes_equal(e.entry_hash, recomputed) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Phase 5 exposes audit_chain_recompute_hash(entry) for testing.
std.io_runtime.remove_file_if_exists(TMP_AUDIT_PATH)
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
expect(e.seq).to_equal(1)
# prev_hash must be the genesis zero hash.
expect(audit_chain_is_zero_hash(e.prev_hash)).to_equal(true)
# entry_hash recomputes deterministically.
val recomputed = audit_chain_recompute_hash(e)
expect(audit_chain_hashes_equal(e.entry_hash, recomputed)).to_equal(true)
```

</details>

### audit chain — tamper detection (AC-5, AC-6e)

#### AC-6e: flipping a byte in middle entry returns Err(ChainBreakAt(2))

1. std io runtime remove file if exists
2. audit chain init
3. event: SecurityEvent AuthSuccess
4. audit chain append
5. audit chain test tamper byte
   - Expected: audit_chain_error_is_chain_break_at(result, 2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Append 3 entries, then corrupt entry #2 (1-based seq).
std.io_runtime.remove_file_if_exists(TMP_AUDIT_PATH)
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

1. std io runtime remove file if exists
2. audit chain init
3. event: SecurityEvent AuthSuccess
4. audit chain append
5. audit chain init
6. event: SecurityEvent AuthSuccess
7. audit chain append
   - Expected: e3.seq equals `3`
   - Expected: audit_chain_verify(TMP_AUDIT_PATH) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pre-seed the file with 2 entries.
std.io_runtime.remove_file_if_exists(TMP_AUDIT_PATH)
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
expect(e3.seq).to_equal(3)
# Full chain still verifies after recovery+append.
expect(audit_chain_verify(TMP_AUDIT_PATH)).to_equal(3)
```

</details>

### audit chain — back-compat with severity (AC-5)

#### AC-5: meets_severity ordering preserved (Info < Warning < Critical)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Phase-3 contract: existing severity ranks are unchanged.
expect(meets_severity(SecuritySeverity.Info, SecuritySeverity.Info)).to_equal(true)
expect(meets_severity(SecuritySeverity.Warning, SecuritySeverity.Info)).to_equal(true)
expect(meets_severity(SecuritySeverity.Critical, SecuritySeverity.Warning)).to_equal(true)
expect(meets_severity(SecuritySeverity.Info, SecuritySeverity.Warning)).to_equal(false)
expect(meets_severity(SecuritySeverity.Info, SecuritySeverity.Critical)).to_equal(false)
```

</details>

#### AC-5: severity_for_event mapping unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
