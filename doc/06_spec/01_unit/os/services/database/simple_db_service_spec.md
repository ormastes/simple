# simple_db_service_spec

> Verifies the simple db service behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_db_service_spec

Verifies the simple db service behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/database/simple_db_service_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

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

- Verify: keeps boot database state across bounded HTTP service requests
- Create a table through POST /db
- Insert a value through the module-owned boot service
- Select the persisted value through POST /db
   - Expected: select.find("Content-Length:") equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-002
step("Verify: keeps boot database state across bounded HTTP service requests")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(select.find("Content-Length:")).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### creates a table, stores a value, selects it, and bounds input

- Verify: creates a table, stores a value, selects it, and bounds input
- Create the settings table
   - Expected: db.execute("CREATE settings") equals `OK CREATE`
- Insert a known setting
   - Expected: db.execute("INSERT settings theme dark") equals `OK INSERT`
- Read the stored value from service state
   - Expected: db.execute("SELECT settings theme") equals `dark`
   - Expected: db.table_count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: db.row_count() equals `1)  # oracle: pinned constant asserted by this scenario`
- Reject input beyond the service boundary
   - Expected: db.execute(oversized) equals `ERR command too long`
   - Expected: db.row_count() equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-002
step("Verify: creates a table, stores a value, selects it, and bounds input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var db = SimpleDbService.new()

step("Create the settings table")
expect(db.execute("CREATE settings")).to_equal("OK CREATE")

step("Insert a known setting")
expect(db.execute("INSERT settings theme dark")).to_equal("OK INSERT")

step("Read the stored value from service state")
expect(db.execute("SELECT settings theme")).to_equal("dark")
expect(db.table_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(db.row_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario

step("Reject input beyond the service boundary")
val oversized = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
expect(db.execute(oversized)).to_equal("ERR command too long")
expect(db.row_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### rejects invalid state transitions without changing stored data

- Verify: rejects invalid state transitions without changing stored data
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
   - Expected: db.row_count() equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-002
step("Verify: rejects invalid state transitions without changing stored data")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(db.row_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### enforces bounded table and row capacity

- Verify: enforces bounded table and row capacity
- Fill the bounded table catalog
   - Expected: db.execute("CREATE table{table_index}") equals `OK CREATE`
   - Expected: db.execute("CREATE overflow") equals `ERR table limit`
- Fill the bounded row store
   - Expected: db.execute("INSERT table0 key{row_index} value{row_index}") equals `OK INSERT`
   - Expected: db.execute("INSERT table0 overflow value") equals `ERR row limit`
   - Expected: db.table_count() equals `16)  # oracle: pinned constant asserted by this scenario`
   - Expected: db.row_count() equals `128)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-002
step("Verify: enforces bounded table and row capacity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(db.table_count()).to_equal(16)  # oracle: pinned constant asserted by this scenario
expect(db.row_count()).to_equal(128)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `12d17f8f001ffcc52f823d1e7188b1a6327a93e07709068206a0f3a14a00e51e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `12d17f8f001ffcc52f823d1e7188b1a6327a93e07709068206a0f3a14a00e51e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `12d17f8f001ffcc52f823d1e7188b1a6327a93e07709068206a0f3a14a00e51e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/services/database/simple_db_service_spec.spl
mirror: doc/06_spec/01_unit/os/services/database/simple_db_service_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/database/simple_db_service_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/services/database/simple_db_service_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/database/simple_db_service_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
