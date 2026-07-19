# Simple Db Service Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Db Service Specification

## Scenarios

### SimpleOS database command core

#### keeps boot database state across bounded HTTP service requests

- Create a table through POST /db
- Insert a value through the module-owned boot service
- Select the persisted value through POST /db
   - Expected: select.find("Content-Length:") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var db = SimpleDbService new
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

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var db = SimpleDbService new
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

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var db = SimpleDbService new
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

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
