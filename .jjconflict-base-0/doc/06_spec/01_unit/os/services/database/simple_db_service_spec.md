# SimpleOS Database Service

> Tests covering SimpleOS database command core.

Status: source contract implemented; live RV64 QEMU proof pending. Stubs: 0.

## Primary flow

1. Send `POST /db` with `CREATE settings`.
2. Reuse the same service instance for `INSERT settings theme dark`.
3. Send `SELECT settings theme` and require the response body `dark`.
4. Require connection-close framing with no computed `Content-Length` header.

The boot HTTP listener calls an exported wrapper around one module-owned,
literal-initialized `SimpleDbService`. That avoids copying mutable service state
through the RV64 listener loop. Non-DB requests keep the existing web path.

## Failure behavior

- Empty, malformed, oversized, duplicate, missing-table, and missing-key
  commands return explicit errors without mutating stored state.
- Requests are capped at 1024 bytes; commands at 256 bytes.
- Body slicing clamps to the request cap instead of depending on the broken RV64
  native `text.len()` result.
- The service holds at most 16 tables and 128 rows.

## Purpose and audience
Verifies the simple db service behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SimpleOS database command core

#### keeps boot database state across bounded HTTP service requests

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps boot database state across bounded HTTP service requests
- Create a table through POST /db
- Insert a value through the module-owned boot service
- Select the persisted value through POST /db
   - Expected: select.find("Content-Length:") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps boot database state across bounded HTTP service requests")
step("Create a table through POST /db")
val create = simple_db_execute_http_request("POST /db HTTP/1.1\r\nContent-Length: 15\r\n\r\nCREATE settings")
expect(create).to_contain("HTTP/1.1 200 OK")

step("Insert a value through the module-owned boot service")
val insert = simple_db_execute_http_request("POST /db HTTP/1.1\r\nContent-Length: 26\r\n\r\nINSERT settings theme dark")
expect(insert).to_contain("HTTP/1.1 200 OK")

step("Select the persisted value through POST /db")
val select = simple_db_execute_http_request("POST /db HTTP/1.1\r\nContent-Length: 21\r\n\r\nSELECT settings theme")
expect(select).to_end_with("\r\n\r\ndark")
expect(select).to_contain("Connection: close")
expect(select.find("Content-Length:")).to_equal(-1)
```

</details>

#### creates a table, stores a value, selects it, and bounds input

- creates a table, stores a value, selects it, and bounds input
- Create the settings table
   - Expected: db.execute("CREATE settings") equals `OK CREATE`
- Insert a known setting
   - Expected: db.execute("INSERT settings theme dark") equals `OK INSERT`
- Read the stored value from service state
   - Expected: db.execute("SELECT settings theme") equals `dark`
   - Expected: db.table_count() equals `1`
   - Expected: db.row_count() equals `1`
- Reject input beyond the service boundary
   - Expected: db.execute(oversized) equals `ERR command too long`
   - Expected: db.row_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("creates a table, stores a value, selects it, and bounds input")
var db = SimpleDbService.new()

step("Create the settings table")
expect(db.execute("CREATE settings")).to_equal("OK CREATE")

step("Insert a known setting")
expect(db.execute("INSERT settings theme dark")).to_equal("OK INSERT")

step("Read the stored value from service state")
expect(db.execute("SELECT settings theme")).to_equal("dark")
expect(db.table_count()).to_equal(1)
expect(db.row_count()).to_equal(1)

step("Reject input beyond the service boundary")
val oversized = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
expect(db.execute(oversized)).to_equal("ERR command too long")
expect(db.row_count()).to_equal(1)
```

</details>

#### rejects invalid state transitions without changing stored data

- rejects invalid state transitions without changing stored data
- Reject commands before a table exists
   - Expected: db.execute("") equals `ERR empty command`
   - Expected: db.execute("INSERT missing key value") equals `ERR table not found`
   - Expected: db.execute("SELECT missing key") equals `ERR table not found`
- Reject duplicate and missing keys
   - Expected: db.execute("CREATE settings") equals `OK CREATE`
   - Expected: db.execute("CREATE settings") equals `ERR table exists`
   - Expected: db.execute("INSERT settings theme dark") equals `OK INSERT`
   - Expected: db.execute("INSERT settings theme light") equals `ERR key exists`
   - Expected: db.execute("SELECT settings missing") equals `ERR key not found`
- Reject malformed commands
   - Expected: db.execute("CREATE ") equals `ERR invalid table`
   - Expected: db.execute("INSERT settings key") equals `ERR invalid command`
   - Expected: db.execute("DROP settings") equals `ERR invalid command`
   - Expected: db.row_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects invalid state transitions without changing stored data")
var db = SimpleDbService.new()

step("Reject commands before a table exists")
expect(db.execute("")).to_equal("ERR empty command")
expect(db.execute("INSERT missing key value")).to_equal("ERR table not found")
expect(db.execute("SELECT missing key")).to_equal("ERR table not found")

step("Reject duplicate and missing keys")
expect(db.execute("CREATE settings")).to_equal("OK CREATE")
expect(db.execute("CREATE settings")).to_equal("ERR table exists")
expect(db.execute("INSERT settings theme dark")).to_equal("OK INSERT")
expect(db.execute("INSERT settings theme light")).to_equal("ERR key exists")
expect(db.execute("SELECT settings missing")).to_equal("ERR key not found")

step("Reject malformed commands")
expect(db.execute("CREATE ")).to_equal("ERR invalid table")
expect(db.execute("INSERT settings key")).to_equal("ERR invalid command")
expect(db.execute("DROP settings")).to_equal("ERR invalid command")
expect(db.row_count()).to_equal(1)
```

</details>

#### enforces bounded table and row capacity

- enforces bounded table and row capacity
- Fill the bounded table catalog
   - Expected: db.execute("CREATE table{table_index}") equals `OK CREATE`
   - Expected: db.execute("CREATE overflow") equals `ERR table limit`
- Fill the bounded row store
   - Expected: db.execute("INSERT table0 key{row_index} value{row_index}") equals `OK INSERT`
   - Expected: db.execute("INSERT table0 overflow value") equals `ERR row limit`
   - Expected: db.table_count() equals `16`
   - Expected: db.row_count() equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("enforces bounded table and row capacity")
var db = SimpleDbService.new()

step("Fill the bounded table catalog")
var table_index = 0
while table_index < 16:
    expect(db.execute("CREATE table{table_index}")).to_equal("OK CREATE")
    table_index = table_index + 1
expect(db.execute("CREATE overflow")).to_equal("ERR table limit")

step("Fill the bounded row store")
var row_index = 0
while row_index < 128:
    expect(db.execute("INSERT table0 key{row_index} value{row_index}")).to_equal("OK INSERT")
    row_index = row_index + 1
expect(db.execute("INSERT table0 overflow value")).to_equal("ERR row limit")
expect(db.table_count()).to_equal(16)
expect(db.row_count()).to_equal(128)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/database/simple_db_service_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS database command core.
- SimpleOS database command core

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

- `REQ-SSPEC-UNIT`
- `REQ-002`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3fa1062551a1a567a364bd1f28dbfb42e3faf8735f78fbe34ce69cc2896a15d8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3fa1062551a1a567a364bd1f28dbfb42e3faf8735f78fbe34ce69cc2896a15d8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3fa1062551a1a567a364bd1f28dbfb42e3faf8735f78fbe34ce69cc2896a15d8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/services/database/simple_db_service_spec.spl
mirror: doc/06_spec/01_unit/os/services/database/simple_db_service_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/services/database/simple_db_service_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/database/simple_db_service_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/database/simple_db_service_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/database/simple_db_service_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/services/database/simple_db_service_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps boot database state across bounded HTTP service requests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/database/simple_db_service_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a table, stores a value, selects it, and bounds input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/database/simple_db_service_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid state transitions without changing stored data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
