# scv_metadata_db_spec

> Purpose: This spec proves the SCV relational metadata store (plan row

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_metadata_db_spec

Purpose: This spec proves the SCV relational metadata store (plan row

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_metadata_db_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV relational metadata store (plan row
SCV-IMPL-B-04): all eleven schema tables (backend_revision, logical_change,
implicit_snapshot, path_state, file/symbol_entity(+version),
identity_relation, parse_index, event_batch) on the TEXTUAL SdnDatabase
backend (std.database.core) with its WriteAheadLog — chosen over the
rt_sqlite emulation because the emulation is non-ACID with unenforced
constraints and cannot carry this schema honestly. Durability claims here
are the SdnDatabase backend's: CRC32-checked atomic snapshot on save(),
per-insert WAL append with replay on load. Also proves migration of the
pipe-delimited identity indexes (file_identity.sdn / identity_edges.sdn)
into file_entity / identity_relation rows.
Audience: Maintainers of the SCV metadata layer.

## Scenarios

### scv metadata db (SdnDatabase backend, WAL)

#### creates all eleven schema tables and persists them

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Open a fresh metadata db and save the schema snapshot
   - Expected: scv_metadb_tables().len() equals `11`
   - Expected: scv_metadb_columns(name).len() > 0 is true
   - Expected: m.count(name) equals `0`
   - Expected: m.save() is true
   - Expected: file_exists(scv_metadb_path(root)) is true
- Reopening finds every table again
   - Expected: m2.count(name) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-METADATA-DB-001
step("Open a fresh metadata db and save the schema snapshot")
val root = _repo("schema")
var m = scv_metadb_open(root)
expect(scv_metadb_tables().len()).to_equal(11)
for name in scv_metadb_tables():
    expect(scv_metadb_columns(name).len() > 0).to_equal(true)
    expect(m.count(name)).to_equal(0)
expect(m.save()).to_equal(true)
expect(file_exists(scv_metadb_path(root))).to_equal(true)
step("Reopening finds every table again")
var m2 = scv_metadb_open(root)
for name in scv_metadb_tables():
    expect(m2.count(name)).to_equal(0)
```

</details>

#### inserts and reads back rows across a save/reload cycle

- Insert one row into several tables and save
   - Expected: m.insert("backend_revision", ["rev_1", "git", "abc123", "c1", "1"]) is true
   - Expected: m.insert("logical_change", ["ch_1", "add feature", "open", "1"]) is true
   - Expected: m.insert("implicit_snapshot", ["snap_1", "ch_1", "c1", "1"]) is true
   - Expected: m.insert("path_state", ["a.txt", "file_1", "live", "c1"]) is true
   - Expected: m.insert("event_batch", ["batch_1", "1", "9", "fs", "1"]) is true
   - Expected: m.insert("parse_index", ["pi_1", "a.spl", "simple", "art_1", "c1"]) is true
   - Expected: m.insert("logical_change", ["ch_2", "too", "few"]) is false
   - Expected: m.save() is true
- Reload and read the rows back by key
   - Expected: m2.count("backend_revision") equals `1`
   - Expected: rev.? is true
   - Expected: r.get("backend") ?? "" equals `git`
   - Expected: r.get("commit") ?? "" equals `c1`
   - Expected: m2.count("logical_change") equals `1`
   - Expected: m2.count("path_state") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-METADATA-DB-001
step("Insert one row into several tables and save")
val root = _repo("rows")
var m = scv_metadb_open(root)
expect(m.insert("backend_revision", ["rev_1", "git", "abc123", "c1", "1"])).to_equal(true)
expect(m.insert("logical_change", ["ch_1", "add feature", "open", "1"])).to_equal(true)
expect(m.insert("implicit_snapshot", ["snap_1", "ch_1", "c1", "1"])).to_equal(true)
expect(m.insert("path_state", ["a.txt", "file_1", "live", "c1"])).to_equal(true)
expect(m.insert("event_batch", ["batch_1", "1", "9", "fs", "1"])).to_equal(true)
expect(m.insert("parse_index", ["pi_1", "a.spl", "simple", "art_1", "c1"])).to_equal(true)
# wrong arity is rejected, never silently truncated
expect(m.insert("logical_change", ["ch_2", "too", "few"])).to_equal(false)
expect(m.save()).to_equal(true)
step("Reload and read the rows back by key")
var m2 = scv_metadb_open(root)
expect(m2.count("backend_revision")).to_equal(1)
val rev = m2.row("backend_revision", "rev_1")
expect(rev.?).to_equal(true)
match rev:
    Some(r):
        expect(r.get("backend") ?? "").to_equal("git")
        expect(r.get("commit") ?? "").to_equal("c1")
    nil:
        pass
expect(m2.count("logical_change")).to_equal(1)
expect(m2.count("path_state")).to_equal(1)
```

</details>

#### replays unsaved inserts from the WAL on reopen

- Save a schema snapshot, then insert WITHOUT saving
   - Expected: m.save() is true
   - Expected: m.insert("logical_change", ["ch_9", "crashy", "open", "1"]) is true
- A fresh open replays the WAL entry into the table
   - Expected: m2.count("logical_change") equals `1`
   - Expected: row.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-METADATA-DB-001
step("Save a schema snapshot, then insert WITHOUT saving")
val root = _repo("wal")
var m = scv_metadb_open(root)
expect(m.save()).to_equal(true)
expect(m.insert("logical_change", ["ch_9", "crashy", "open", "1"])).to_equal(true)
# no m.save() — simulate a crash before checkpoint
step("A fresh open replays the WAL entry into the table")
var m2 = scv_metadb_open(root)
expect(m2.count("logical_change")).to_equal(1)
val row = m2.row("logical_change", "ch_9")
expect(row.?).to_equal(true)
```

</details>

#### keeps multi-version tables keyed on synthetic unique first columns

- Two versions of one entity must both survive (no index clobber)
   - Expected: m.next_key("file_entity_version", "fv") equals `fv_1`
   - Expected: m.insert("file_entity_version", ["fv_1", "file_1", "c1", "cid_a", "a.txt"]) is true
   - Expected: m.next_key("file_entity_version", "fv") equals `fv_2`
   - Expected: m.insert("file_entity_version", ["fv_2", "file_1", "c2", "cid_b", "a.txt"]) is true
   - Expected: m.insert("symbol_entity_version", ["sv_1", "sym_1", "c1", "10", "fn f()"]) is true
   - Expected: m.insert("symbol_entity_version", ["sv_2", "sym_1", "c2", "12", "fn f(x)"]) is true
   - Expected: m.save() is true
   - Expected: m2.count("file_entity_version") equals `2`
   - Expected: m2.count("symbol_entity_version") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-METADATA-DB-001
step("Two versions of one entity must both survive (no index clobber)")
val root = _repo("vers")
var m = scv_metadb_open(root)
expect(m.next_key("file_entity_version", "fv")).to_equal("fv_1")
expect(m.insert("file_entity_version", ["fv_1", "file_1", "c1", "cid_a", "a.txt"])).to_equal(true)
expect(m.next_key("file_entity_version", "fv")).to_equal("fv_2")
expect(m.insert("file_entity_version", ["fv_2", "file_1", "c2", "cid_b", "a.txt"])).to_equal(true)
expect(m.insert("symbol_entity_version", ["sv_1", "sym_1", "c1", "10", "fn f()"])).to_equal(true)
expect(m.insert("symbol_entity_version", ["sv_2", "sym_1", "c2", "12", "fn f(x)"])).to_equal(true)
expect(m.save()).to_equal(true)
var m2 = scv_metadb_open(root)
expect(m2.count("file_entity_version")).to_equal(2)
expect(m2.count("symbol_entity_version")).to_equal(2)
```

</details>

#### migrates pipe-delimited identity indexes into relational rows

- Build real identity state via the pipe-file write path
   - Expected: id equals `file_1`
- Migrate into file_entity / identity_relation and verify counts
   - Expected: verdict equals `files=2,edges=4`
   - Expected: m2.count("file_entity") equals `2`
   - Expected: m2.count("identity_relation") equals `4`
   - Expected: fe.? is true
   - Expected: r.get("current_path") ?? "" equals `b.txt`
   - Expected: r.get("state") ?? "" equals `live`
- Migration is idempotent — rerunning imports nothing new
   - Expected: verdict2 equals `files=0,edges=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-METADATA-DB-001
step("Build real identity state via the pipe-file write path")
val root = _repo("mig")
val id = scv_identity_allocate(root, "a.txt", "c1")
expect(id).to_equal("file_1")
scv_identity_record_move(root, "a.txt", "b.txt", "c2", "exact_content,unique_pair", 1000, "accepted")
scv_identity_record_copy(root, "b.txt", "c.txt", "c3", "copy_evidence")
step("Migrate into file_entity / identity_relation and verify counts")
var m = scv_metadb_open(root)
val verdict = scv_metadb_migrate_identity(root, m)
expect(verdict).to_equal("files=2,edges=4")
var m2 = scv_metadb_open(root)
expect(m2.count("file_entity")).to_equal(2)
expect(m2.count("identity_relation")).to_equal(4)
val fe = m2.row("file_entity", "file_1")
expect(fe.?).to_equal(true)
match fe:
    Some(r):
        expect(r.get("current_path") ?? "").to_equal("b.txt")
        expect(r.get("state") ?? "").to_equal("live")
    nil:
        pass
step("Migration is idempotent — rerunning imports nothing new")
var m3 = scv_metadb_open(root)
val verdict2 = scv_metadb_migrate_identity(root, m3)
expect(verdict2).to_equal("files=0,edges=0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-METADATA-DB-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b7a5dc7fdd2d1f61fbad452271e89d63092a1f29bf4087f83e491269a933d68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b7a5dc7fdd2d1f61fbad452271e89d63092a1f29bf4087f83e491269a933d68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b7a5dc7fdd2d1f61fbad452271e89d63092a1f29bf4087f83e491269a933d68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_metadata_db_spec.spl
mirror: doc/06_spec/integration/app/scv_metadata_db_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/app/scv_metadata_db_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_metadata_db_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_metadata_db_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_metadata_db_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_metadata_db_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates all eleven schema tables and persists them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_metadata_db_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts and reads back rows across a save/reload cycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_metadata_db_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replays unsaved inserts from the WAL on reopen' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
