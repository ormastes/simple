# Claude Full Bridge FlushGate

> Mirrors `bridge/flushGate.ts`, the queueing state machine that prevents new

<!-- sdn-diagram:id=flushGate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=flushGate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

flushGate_spec -> std
flushGate_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=flushGate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge FlushGate

Mirrors `bridge/flushGate.ts`, the queueing state machine that prevents new

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/flushGate_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `bridge/flushGate.ts`, the queueing state machine that prevents new
messages from interleaving with an initial history flush.

## Scenarios

### Claude full bridge FlushGate

#### should queue messages only while active and drain them on end

- Create a gate and confirm the initial inactive state
   - Expected: flushGateIsActive(gate) is false
   - Expected: flushGatePendingCount(gate) equals `0`
   - Expected: gate.enqueue("direct") is false
- Start the flush and queue messages
- gate start
   - Expected: gate.isActive() is true
   - Expected: gate.enqueue("a") is true
   - Expected: gate.enqueue2("b", "c") is true
   - Expected: gate.pendingCount() equals `3`
   - Expected: gate.firstPending() equals `a`
   - Expected: gate.lastPending() equals `c`
- End the flush and drain pending messages
   - Expected: gate.isActive() is false
   - Expected: gate.pendingCount() equals `0`
   - Expected: drained.len() equals `3`
   - Expected: drained[0] equals `a`
   - Expected: drained[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a gate and confirm the initial inactive state")
val gate = flushGateNew()
expect(flushGateIsActive(gate)).to_equal(false)
expect(flushGatePendingCount(gate)).to_equal(0)
expect(gate.enqueue("direct")).to_equal(false)

step("Start the flush and queue messages")
gate.start()
expect(gate.isActive()).to_equal(true)
expect(gate.enqueue("a")).to_equal(true)
expect(gate.enqueue2("b", "c")).to_equal(true)
expect(gate.pendingCount()).to_equal(3)
expect(gate.firstPending()).to_equal("a")
expect(gate.lastPending()).to_equal("c")

step("End the flush and drain pending messages")
val drained = gate.end()
expect(gate.isActive()).to_equal(false)
expect(gate.pendingCount()).to_equal(0)
expect(drained.len()).to_equal(3)
expect(drained[0]).to_equal("a")
expect(drained[2]).to_equal("c")
```

</details>

#### should drop or preserve pending messages according to lifecycle method

- Drop pending messages on permanent close
- gate start
   - Expected: gate.enqueueMany(["x", "y"]) is true
   - Expected: gate.drop() equals `2`
   - Expected: gate.isActive() is false
   - Expected: gate.hasPending() is false
- Deactivate without clearing pending messages for transport replacement
- gate start
   - Expected: gate.enqueue("replacement") is true
- gate deactivate
   - Expected: gate.isActive() is false
   - Expected: gate.pendingCount() equals `1`
   - Expected: gate.end()[0] equals `replacement`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Drop pending messages on permanent close")
val gate = flushGateNew()
gate.start()
expect(gate.enqueueMany(["x", "y"])).to_equal(true)
expect(gate.drop()).to_equal(2)
expect(gate.isActive()).to_equal(false)
expect(gate.hasPending()).to_equal(false)

step("Deactivate without clearing pending messages for transport replacement")
gate.start()
expect(gate.enqueue("replacement")).to_equal(true)
gate.deactivate()
expect(gate.isActive()).to_equal(false)
expect(gate.pendingCount()).to_equal(1)
expect(gate.end()[0]).to_equal("replacement")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
