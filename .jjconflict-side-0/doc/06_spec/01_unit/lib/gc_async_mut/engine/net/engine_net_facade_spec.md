# Engine Net Facade Specification

> Tests covering gc_async_mut engine net facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Net Facade Specification

## Scenarios

### gc_async_mut engine net facade

#### re-exports server, client, sync, and rpc behavior

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports server, client, sync, and rpc behavior
   - Expected: client_id equals `1`
   - Expected: server.client_count() equals `1`
   - Expected: server.get_tick() equals `1`
   - Expected: client.is_connected() is true
   - Expected: client.input_count() equals `1`
   - Expected: client.get_server_tick() equals `3`
   - Expected: client.state_count() equals `1`
   - Expected: state_sync.register_entity(7, client_id) is true
   - Expected: state_sync.entity_count() equals `1`
   - Expected: state_sync.get_dirty_count(7) equals `1`
   - Expected: state_sync.get_field_value(7, "x") equals `10`
   - Expected: state_sync.get_dirty_count(7) equals `0`
   - Expected: rpc.register("move", "player", true) is true
   - Expected: rpc.is_registered("move") is true
   - Expected: rpc.dispatch("move", client_id, ["left"], 1.0) is true
   - Expected: rpc.call_count() equals `1`
   - Expected: rpc.unregister("move") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports server, client, sync, and rpc behavior")
var server = GameServer.new(2, 60)
server.start()
val client_id = server.connect_client("127.0.0.1:9000")
expect(client_id).to_equal(1)
expect(server.client_count()).to_equal(1)
server.tick()
expect(server.get_tick()).to_equal(1)

var client = GameClient.new("127.0.0.1:9000")
client.connect(client_id)
client.send_input(1.0, 0.0, 0.0)
expect(client.is_connected()).to_equal(true)
expect(client.input_count()).to_equal(1)
client.receive_state(3, 10.0, 2.0, 0.0, 0.1, 0.0, 0.0)
expect(client.get_server_tick()).to_equal(3)
expect(client.state_count()).to_equal(1)

var state_sync = StateSync.new(2)
expect(state_sync.register_entity(7, client_id)).to_equal(true)
state_sync.set_field(7, "x", "10")
expect(state_sync.entity_count()).to_equal(1)
expect(state_sync.get_dirty_count(7)).to_equal(1)
expect(state_sync.get_field_value(7, "x")).to_equal("10")
state_sync.tick()
state_sync.mark_synced(7)
expect(state_sync.get_dirty_count(7)).to_equal(0)

var rpc = RPCDispatcher.new(4)
expect(rpc.register("move", "player", true)).to_equal(true)
expect(rpc.is_registered("move")).to_equal(true)
expect(rpc.dispatch("move", client_id, ["left"], 1.0)).to_equal(true)
expect(rpc.call_count()).to_equal(1)
expect(rpc.unregister("move")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/engine/net/engine_net_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut engine net facade.
- gc_async_mut engine net facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2a447446c05c2edcd12c06e9f1e93070683abc101dcdd8f4a14a73593daa0e42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a447446c05c2edcd12c06e9f1e93070683abc101dcdd8f4a14a73593daa0e42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a447446c05c2edcd12c06e9f1e93070683abc101dcdd8f4a14a73593daa0e42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_async_mut/engine/net/engine_net_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/engine/net/engine_net_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/engine/net/engine_net_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/engine/net/engine_net_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/engine/net/engine_net_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/engine/net/engine_net_facade_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports server, client, sync, and rpc behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
