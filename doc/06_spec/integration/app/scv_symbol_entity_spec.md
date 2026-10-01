# scv_symbol_entity_spec

> Purpose: This spec proves SCV's SymbolEntityId layer (plan row

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_symbol_entity_spec

Purpose: This spec proves SCV's SymbolEntityId layer (plan row

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_symbol_entity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV's SymbolEntityId layer (plan row
SCV-IMPL-I-03): declaration extraction from Simple (.spl) source via the
interim structural line scanner (module/type/trait/fn/field/variant/const —
query-pack hookup is an explicit TODO on SCV-IMPL-P-06), and persistent
symbol_entity(+version) rows in the SCV-IMPL-B-04 metadata db (textual
SdnDatabase backend + WAL — not the rt_sqlite emulation). Symbol ids are
stable across commits: re-ingesting allocates no new id for an unchanged
declaration but always appends a version row.
Audience: Maintainers of the SCV identity layer.

## Scenarios

### scv symbol entity ids and declaration extraction

#### extracts module, type, trait, fn, field, variant and const declarations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Scan a representative .spl source


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-SYMBOL-ENTITY-001
step("Scan a representative .spl source")
val rows = scv_symbol_extract_decls(_sample())
var joined = ""
for r in rows:
    joined = joined + r + "\n"
expect(joined).to_contain("const|LIMIT|1|")
expect(joined).to_contain("fn|top|3|")
expect(joined).to_contain("type|Point|6|")
expect(joined).to_contain("field|x|7|Point")
expect(joined).to_contain("field|y|8|Point")
expect(joined).to_contain("fn|norm|10|Point")
expect(joined).to_contain("enum|Color|13|")
expect(joined).to_contain("variant|Red|14|Color")
expect(joined).to_contain("variant|Green|15|Color")
expect(joined).to_contain("trait|Shape|17|")
expect(joined).to_contain("fn|area|18|Shape")
```

</details>

#### persists symbol_entity rows with repo-unique stable ids

- Ingest a file at commit c1
   - Expected: verdict equals `symbols=2,new=2,versions=2`
- Rows survive a reopen with sym_<n> ids
   - Expected: m2.count("symbol_entity") equals `2`
   - Expected: m2.count("symbol_entity_version") equals `2`
   - Expected: row.? is true
   - Expected: r.get("file_id") ?? "" equals `file_1`
   - Expected: r.get("kind") ?? "" equals `fn`
   - Expected: r.get("state") ?? "" equals `live`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-SYMBOL-ENTITY-001
step("Ingest a file at commit c1")
val root = _repo("ingest")
var m = scv_metadb_open(root)
val verdict = scv_symbol_ingest(m, "file_1", "fn alpha():\n    pass\n\nfn beta():\n    pass\n", "c1")
expect(verdict).to_equal("symbols=2,new=2,versions=2")
step("Rows survive a reopen with sym_<n> ids")
var m2 = scv_metadb_open(root)
expect(m2.count("symbol_entity")).to_equal(2)
expect(m2.count("symbol_entity_version")).to_equal(2)
val row = m2.row("symbol_entity", "sym_1")
expect(row.?).to_equal(true)
match row:
    Some(r):
        expect(r.get("file_id") ?? "").to_equal("file_1")
        expect(r.get("kind") ?? "").to_equal("fn")
        expect(r.get("state") ?? "").to_equal("live")
    nil:
        pass
```

</details>

#### reuses ids across commits and appends version rows

- Ingest the same file at c1 then at c2 with one added fn
   - Expected: scv_symbol_ingest(m, "file_1", "fn alpha():\n    pass\n", "c1") equals `symbols=1,new=1,versions=1`
- alpha kept its id (new=1 is gamma only); versions accumulate
   - Expected: v2 equals `symbols=2,new=1,versions=2`
   - Expected: m3.count("symbol_entity") equals `2`
   - Expected: m3.count("symbol_entity_version") equals `3`
- Same-named symbols in DIFFERENT files get different ids
   - Expected: v3 equals `symbols=1,new=1,versions=1`
   - Expected: m4.count("symbol_entity") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-SYMBOL-ENTITY-001
step("Ingest the same file at c1 then at c2 with one added fn")
val root = _repo("stable")
var m = scv_metadb_open(root)
expect(scv_symbol_ingest(m, "file_1", "fn alpha():\n    pass\n", "c1")).to_equal("symbols=1,new=1,versions=1")
var m2 = scv_metadb_open(root)
val v2 = scv_symbol_ingest(m2, "file_1", "fn alpha():\n    pass\n\nfn gamma():\n    pass\n", "c2")
step("alpha kept its id (new=1 is gamma only); versions accumulate")
expect(v2).to_equal("symbols=2,new=1,versions=2")
var m3 = scv_metadb_open(root)
expect(m3.count("symbol_entity")).to_equal(2)
expect(m3.count("symbol_entity_version")).to_equal(3)
step("Same-named symbols in DIFFERENT files get different ids")
val v3 = scv_symbol_ingest(m3, "file_2", "fn alpha():\n    pass\n", "c2")
expect(v3).to_equal("symbols=1,new=1,versions=1")
var m4 = scv_metadb_open(root)
expect(m4.count("symbol_entity")).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-SYMBOL-ENTITY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c65f70006830ec474bd70379e4fa819729727202b5be813e500ce45c462af52c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c65f70006830ec474bd70379e4fa819729727202b5be813e500ce45c462af52c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c65f70006830ec474bd70379e4fa819729727202b5be813e500ce45c462af52c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_symbol_entity_spec.spl
mirror: doc/06_spec/integration/app/scv_symbol_entity_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/app/scv_symbol_entity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_symbol_entity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_symbol_entity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_symbol_entity_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_symbol_entity_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts module, type, trait, fn, field, variant and const declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_symbol_entity_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists symbol_entity rows with repo-unique stable ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_symbol_entity_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses ids across commits and appends version rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
