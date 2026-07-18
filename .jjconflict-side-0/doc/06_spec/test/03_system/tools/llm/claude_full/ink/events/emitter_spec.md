# Claude Full Ink EventEmitter

> Checks max-listener disabling and immediate propagation-aware emit.

<!-- sdn-diagram:id=emitter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=emitter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

emitter_spec -> std
emitter_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=emitter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Ink EventEmitter

Checks max-listener disabling and immediate propagation-aware emit.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/events/emitter_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks max-listener disabling and immediate propagation-aware emit.

## Scenarios

### Claude full ink EventEmitter

#### disables max listener warnings

- Constructor sets max listeners to zero
   - Expected: emitter.maxListeners equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Constructor sets max listeners to zero")
val emitter = EventEmitter.new()
expect(emitter.maxListeners).to_equal(0)
```

</details>

#### emits listeners and stops immediate propagation

- Normal emit calls listeners; stopped event breaks after first
- emitter on
- emitter on
   - Expected: emitter.emit("click", false) is true
   - Expected: emitter.calls equals `["a", "b"]`
- stopped on
- stopped on
   - Expected: stopped.emit("click", true) is true
   - Expected: stopped.calls equals `["a"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Normal emit calls listeners; stopped event breaks after first")
val emitter = EventEmitter.new()
emitter.on("a")
emitter.on("b")
expect(emitter.emit("click", false)).to_equal(true)
expect(emitter.calls).to_equal(["a", "b"])
val stopped = EventEmitter.new()
stopped.on("a")
stopped.on("b")
expect(stopped.emit("click", true)).to_equal(true)
expect(stopped.calls).to_equal(["a"])
```

</details>

#### handles error and empty listener cases

- Error delegates to node and empty emit returns false
   - Expected: empty.emit("click", false) is false
   - Expected: empty.emit("error", false) is true
   - Expected: empty.calls equals `["node:error"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Error delegates to node and empty emit returns false")
val empty = EventEmitter.new()
expect(empty.emit("click", false)).to_equal(false)
expect(empty.emit("error", false)).to_equal(true)
expect(empty.calls).to_equal(["node:error"])
```

</details>

#### exports source-backed constants

- Pin emitter contract
   - Expected: disablesDefaultMaxListenersWarning() is true
   - Expected: defaultMaxListeners() equals `0`
   - Expected: errorEventsDelegateToNode() is true
   - Expected: emitReturnsFalseWithoutListeners() is true
   - Expected: emitStopsOnImmediatePropagation() is true
   - Expected: eventEmitterSourceLinesModeled() equals `39`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin emitter contract")
expect(disablesDefaultMaxListenersWarning()).to_equal(true)
expect(defaultMaxListeners()).to_equal(0)
expect(errorEventsDelegateToNode()).to_equal(true)
expect(emitReturnsFalseWithoutListeners()).to_equal(true)
expect(emitStopsOnImmediatePropagation()).to_equal(true)
expect(eventEmitterSourceLinesModeled()).to_equal(39)
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
