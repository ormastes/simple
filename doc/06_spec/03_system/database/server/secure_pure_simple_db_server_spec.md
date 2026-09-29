# Secure Pure-Simple database server

> These operator scenarios prove authentication, bounded query behavior,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Secure Pure-Simple database server

These operator scenarios prove authentication, bounded query behavior,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/database/server/secure_pure_simple_db_server_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

These operator scenarios prove authentication, bounded query behavior,
connection cleanup, durable commit identity, and restart-safe conflict tokens
through the production database capsule interfaces.

## Scenarios

### Secure Pure-Simple database server

#### Authenticate the database principal

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Authentication and lifecycle (expected show, folded, detail, or skip)


- Authenticate the database principal
- Authenticate the database principal
   - Expected: server.handle_message("OPEN") equals `expected`
   - Expected: server.handle_message("OPEN as=alice") equals `expected`
   - Expected: server.handle_message("OPEN as=alice credential=wrong") equals `expected`
   - Expected: server.handle_message("OPEN as=unknown credential=alice-secret") equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Authenticate the database principal")
step("Authenticate the database principal")
var server = secure_db_server_fixture()
val expected = 'ERR code=auth msg="authentication failed"'
expect(server.handle_message("OPEN")).to_equal(expected)
expect(server.handle_message("OPEN as=alice")).to_equal(expected)
expect(server.handle_message("OPEN as=alice credential=wrong")).to_equal(expected)
expect(server.handle_message("OPEN as=unknown credential=alice-secret")).to_equal(expected)
expect(server.handle_message(
    "OPEN as=alice credential=alice-secret"
)).to_equal("OK session=1")
```

</details>

#### Shut down and release the connection

- Shut down and release the connection
- Shut down and release the connection
   - Expected: outcome.served equals `3`
   - Expected: server.registry.open_session_count() equals `0`
   - Expected: server.connection_capacity() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Shut down and release the connection")
step("Shut down and release the connection")
var server = secure_db_server_fixture()
val outcome = server.serve(MemoryTransport.with_messages([
    "OPEN as=alice credential=alice-secret",
    "BEGIN session=1",
    "PUT session=1 tbl=users id=abandoned name=private"
]))
expect(outcome.served).to_equal(3)
expect(server.registry.open_session_count()).to_equal(0)
expect(server.connection_capacity()).to_equal(1)
```

</details>

#### Reject a listener configuration with no connection capacity

- Reject a listener configuration with no connection capacity
- Bind the production listener
   - Expected: server.connection_count() equals `0`
   - Expected: server.listener_running is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Reject a listener configuration with no connection capacity")
step("Bind the production listener")
var server = secure_db_server_fixture()
match server.listen("127.0.0.1", 0, 0):
    Ok(_): expect(false).to_equal(true)
    Err(error): expect(error.message).to_contain("max_connections must be positive")
expect(server.connection_count()).to_equal(0)
expect(server.listener_running).to_equal(false)
```

</details>

#### Bound a batch or range response

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Bounded transaction queries (expected show, folded, detail, or skip)


- Bound a batch or range response
- Bound a batch or range response
   - Expected: server.handle_message("BEGIN session=1") equals `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Bound a batch or range response")
step("Bound a batch or range response")
var server = secure_db_server_fixture()
expect(server.handle_message(
    "OPEN as=alice credential=alice-secret"
)).to_equal("OK session=1")
expect(server.handle_message("BEGIN session=1")).to_equal("OK")
expect(server.handle_message(
    "BATCH_PUT session=1 tbl=users ids=u3,u1,u2 name=bounded"
)).to_equal("OK queued=3")
expect(server.handle_message(
    "RANGE_GET session=1 tbl=users start=u1 end=u3 limit=2"
)).to_equal("OK ids=u1,u2")
expect_bounded_query(server)
```

</details>

#### Use canonical commit identity and bounded query contracts

- Use canonical commit identity and bounded query contracts
- Bound a batch or range response
   - Expected: identity_present is true
   - Expected: typed.principal equals `alice`
   - Expected: bounds.max_response_bytes equals `MAX_RESPONSE_BYTES`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Use canonical commit identity and bounded query contracts")
step("Bound a batch or range response")
val identity = validated_commit_identity("commit-1", "alice")
var identity_present = false
match identity:
    Some(_): identity_present = true
    nil: identity_present = false
expect(identity_present).to_equal(true)
val typed: CommitIdentity = identity ?? CommitIdentity(value: "", principal: "")
expect(typed.principal).to_equal("alice")
val bounds: BoundedQuery = server_query_bounds()
expect(bounds.max_response_bytes).to_equal(MAX_RESPONSE_BYTES)
```

</details>

#### Apply the encoded response bound on the production dispatch path

- Apply the encoded response bound on the production dispatch path
- Bound a batch or range response


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Apply the encoded response bound on the production dispatch path")
step("Bound a batch or range response")
var store = SdnDatabase.new("")
var users = SdnTable.new("users", ["id", "name", "valid"])
val huge = ["x"; 8190].join("")
users.add_row(SdnRow(fields: {"id": "u1", "name": huge, "valid": "true"}, _version: 0))
store.set_table("users", users)
var policy = CapabilityTable.new()
policy.register_authenticated(capability_with("alice", [grant_key("users", "read")]), "alice-secret")
var server = DbServerCapsule.new(store, policy)
server.handle_message("OPEN as=alice credential=alice-secret")
expect(server.bounded_message_response(
    "GET session=1 tbl=users id=u1 col=name"
)).to_contain("code=limit")
```

</details>

#### Deny every ungranted table and operation combination

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Capability denial matrix (expected show, folded, detail, or skip)


- Deny every ungranted table and operation combination
- Authenticate the database principal
   - Expected: server.handle_message("OPEN as=reader credential=reader-secret") equals `OK session=1`
   - Expected: server.handle_message("BEGIN session=1") equals `OK`
   - Expected: server.handle_message("OPEN as=none credential=none-secret") equals `OK session=2`
   - Expected: server.handle_message("BEGIN session=2") equals `OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Deny every ungranted table and operation combination")
step("Authenticate the database principal")
var store = SdnDatabase.new("")
store.set_table("users", SdnTable.new("users", ["id", "name", "valid"]))
store.set_table("audit", SdnTable.new("audit", ["id", "event", "valid"]))
var policy = CapabilityTable.new()
policy.register_authenticated(capability_with("reader", [
    grant_key("users", "read")
]), "reader-secret")
policy.register_authenticated(empty_capability("none"), "none-secret")
var server = DbServerCapsule.new(store, policy)
expect(server.handle_message("OPEN as=reader credential=reader-secret")).to_equal("OK session=1")
expect(server.handle_message("BEGIN session=1")).to_equal("OK")
expect(server.handle_message("PUT session=1 tbl=users id=u1 name=x")).to_contain("code=denied")
expect(server.handle_message("GET session=1 tbl=audit id=a1 col=event")).to_contain("code=denied")
expect(server.handle_message("OPEN as=none credential=none-secret")).to_equal("OK session=2")
expect(server.handle_message("BEGIN session=2")).to_equal("OK")
expect(server.handle_message("GET session=2 tbl=users id=u1 col=name")).to_contain("code=denied")
expect(server.handle_message("DEL session=2 tbl=users id=u1")).to_contain("code=denied")
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

- `REQ-SSPEC-SYSTEM`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `651e8687add16cc39bd109332c8f2f89ac3c85ebd1da5efd7ef834a4470032c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `651e8687add16cc39bd109332c8f2f89ac3c85ebd1da5efd7ef834a4470032c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `651e8687add16cc39bd109332c8f2f89ac3c85ebd1da5efd7ef834a4470032c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/database/server/secure_pure_simple_db_server_spec.spl
mirror: doc/06_spec/03_system/database/server/secure_pure_simple_db_server_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/database/server/secure_pure_simple_db_server_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/database/server/secure_pure_simple_db_server_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/database/server/secure_pure_simple_db_server_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/database/server/secure_pure_simple_db_server_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/database/server/secure_pure_simple_db_server_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Authenticate the database principal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/database/server/secure_pure_simple_db_server_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Shut down and release the connection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/database/server/secure_pure_simple_db_server_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Reject a listener configuration with no connection capacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
