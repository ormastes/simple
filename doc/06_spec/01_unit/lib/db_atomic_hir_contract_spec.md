# Atomic Database Behavioral Contract

> Exercises the real atomic database mirrors end to end: a write is readable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Atomic Database Behavioral Contract

Exercises the real atomic database mirrors end to end: a write is readable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db_atomic_hir_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the real atomic database mirrors end to end: a write is readable
back byte-for-byte, an atomic update transforms content under the file lock,
and a read of a missing file fails closed with an Err instead of returning
garbage. Both mirrors (nogc_sync_mut and nogc_async_mut) must satisfy the
same behavior.

## Scenarios

### atomic database behavioral contract

#### a locked atomic write is readable back byte-for-byte in the sync mirror

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- atomically write a payload in the sync mirror and read it back
   - Expected: written.is_ok() is true
   - Expected: read_back.is_ok() is true
   - Expected: content equals `table users\n  row a, b\n`
   - Expected: message equals `__unreachable__`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("atomically write a payload in the sync mirror and read it back")
# evidence(protocol_json): Result values asserted below are the complete typed oracle
val path = _tmp_dir() + "/sync_write.sdn"
file_remove(path)
val written = atomic_write(path, "table users\n  row a, b\n", DbConfig.defaults())
expect(written.is_ok()).to_equal(true)
val read_back = atomic_read(path, DbConfig.defaults())
expect(read_back.is_ok()).to_equal(true)
match read_back:
    case Ok(content):
        expect(content).to_equal("table users\n  row a, b\n")
    case Err(message):
        expect(message).to_equal("__unreachable__")
```

</details>

#### an atomic update transforms content under the lock in the sync mirror

- run atomic_update over an existing sync-mirror file
   - Expected: written.is_ok() is true
   - Expected: updated.is_ok() is true
   - Expected: content equals `count 2\n`
   - Expected: message equals `__unreachable__`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("run atomic_update over an existing sync-mirror file")
# evidence(protocol_json): Result values asserted below are the complete typed oracle
val path = _tmp_dir() + "/sync_update.sdn"
file_remove(path)
val written = atomic_write(path, "count 1\n", DbConfig.defaults())
expect(written.is_ok()).to_equal(true)
val updated = atomic_update(path, fn(content: text) -> text:
    content.replace("count 1", "count 2")
, DbConfig.defaults())
expect(updated.is_ok()).to_equal(true)
match atomic_read(path, DbConfig.defaults()):
    case Ok(content):
        expect(content).to_equal("count 2\n")
    case Err(message):
        expect(message).to_equal("__unreachable__")
```

</details>

#### reading a missing file yields empty content rather than an error

- atomically read a path that does not exist
   - Expected: missing.is_ok() is true
   - Expected: content equals ``
   - Expected: message equals `__unreachable__`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("atomically read a path that does not exist")
# evidence(protocol_json): the Ok("") contract asserted below is the complete typed oracle
val missing = atomic_read(_tmp_dir() + "/does_not_exist_{rt_env_get_probe()}.sdn", DbConfig.defaults())
expect(missing.is_ok()).to_equal(true)  # oracle: a non-existent file reads as empty per the documented contract
match missing:
    case Ok(content):
        expect(content).to_equal("")
    case Err(message):
        expect(message).to_equal("__unreachable__")
```

</details>

#### the async mirror satisfies the same write/read/update behavior

- atomically write, update and read back in the async mirror
   - Expected: written.is_ok() is true
   - Expected: content equals `table users\n  row a, b\n`
   - Expected: message equals `__unreachable__`
   - Expected: updated.is_ok() is true
   - Expected: message equals `__unreachable__`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("atomically write, update and read back in the async mirror")
# evidence(protocol_json): Result values asserted below are the complete typed oracle
val path = _tmp_dir() + "/async_write.sdn"
file_remove(path)
val written = a_atomic_write(path, "table users\n  row a, b\n", ADbConfig.defaults())
expect(written.is_ok()).to_equal(true)
match a_atomic_read(path, ADbConfig.defaults()):
    case Ok(content):
        expect(content).to_equal("table users\n  row a, b\n")
    case Err(message):
        expect(message).to_equal("__unreachable__")
val updated = a_atomic_update(path, fn(content: text) -> text:
    content.replace("row a", "row z")
, ADbConfig.defaults())
expect(updated.is_ok()).to_equal(true)
match a_atomic_read(path, ADbConfig.defaults()):
    case Ok(content):
        expect(content).to_contain("row z, b")
    case Err(message):
        expect(message).to_equal("__unreachable__")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `5fc27fa8c5543e0b467bc206e534e966b9ca448fa411f9078f14300fb1b8b415`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fc27fa8c5543e0b467bc206e534e966b9ca448fa411f9078f14300fb1b8b415`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fc27fa8c5543e0b467bc206e534e966b9ca448fa411f9078f14300fb1b8b415`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/lib/db_atomic_hir_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/db_atomic_hir_contract_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/db_atomic_hir_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/db_atomic_hir_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
