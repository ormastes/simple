# Claude Full Terminal Querier

> Checks terminal query builders and DA1 sentinel queue draining.

<!-- sdn-diagram:id=terminal-querier_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terminal-querier_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terminal-querier_spec -> std
terminal-querier_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terminal-querier_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Terminal Querier

Checks terminal query builders and DA1 sentinel queue draining.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/terminal-querier_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks terminal query builders and DA1 sentinel queue draining.

## Scenarios

### Claude full TerminalQuerier

#### should build terminal query request sequences

- Build core terminal query escape sequences
   - Expected: decrqm(2026).request equals `\u001B[?2026$p`
   - Expected: da1().request equals `\u001B[c`
   - Expected: da2().request equals `\u001B[>c`
   - Expected: kittyKeyboard().request equals `\u001B[?u`
   - Expected: cursorPosition().request equals `\u001B[?6n`
   - Expected: oscColor(11).request equals `\u001B]11;?\u0007`
   - Expected: xtversion().request equals `\u001B[>0q`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build core terminal query escape sequences")
expect(decrqm(2026).request).to_equal("\u001B[?2026$p")
expect(da1().request).to_equal("\u001B[c")
expect(da2().request).to_equal("\u001B[>c")
expect(kittyKeyboard().request).to_equal("\u001B[?u")
expect(cursorPosition().request).to_equal("\u001B[?6n")
expect(oscColor(11).request).to_equal("\u001B]11;?\u0007")
expect(xtversion().request).to_equal("\u001B[>0q")
```

</details>

#### should match response types with mode and code constraints

- Check query matcher behavior
   - Expected: queryMatches(decrqm(2026), decrpmResponse(2026)) is true
   - Expected: queryMatches(decrqm(2026), decrpmResponse(2027)) is false
   - Expected: queryMatches(oscColor(11), oscResponse(11)) is true
   - Expected: queryMatches(oscColor(10), oscResponse(11)) is false
   - Expected: queryMatches(da1(), response("da1")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check query matcher behavior")
expect(queryMatches(decrqm(2026), decrpmResponse(2026))).to_equal(true)
expect(queryMatches(decrqm(2026), decrpmResponse(2027))).to_equal(false)
expect(queryMatches(oscColor(11), oscResponse(11))).to_equal(true)
expect(queryMatches(oscColor(10), oscResponse(11))).to_equal(false)
expect(queryMatches(da1(), response("da1"))).to_equal(true)
```

</details>

#### should send queries and resolve matching responses out of queue order

- Resolve the first matching query even when not at the head
- querier send
- querier send
- querier onResponse
   - Expected: querier.pendingCount() equals `1`
   - Expected: querier.resolved[0] equals `osc:osc`
   - Expected: querier.writtenText() equals `\u001B[?2026$p\u001B]11;?\u0007`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the first matching query even when not at the head")
val querier = TerminalQuerier.new()
querier.send(decrqm(2026))
querier.send(oscColor(11))
querier.onResponse(oscResponse(11))
expect(querier.pendingCount()).to_equal(1)
expect(querier.resolved[0]).to_equal("osc:osc")
expect(querier.writtenText()).to_equal("\u001B[?2026$p\u001B]11;?\u0007")
```

</details>

#### should flush with a DA1 sentinel and mark previous queries unsupported

- Flush a query batch and receive DA1
- querier send
- querier flush
- querier send
- querier onResponse
   - Expected: querier.resolved equals `["decrpm:undefined", "sentinel:resolved"]`
   - Expected: querier.pendingCount() equals `1`
   - Expected: querier.queue[0].query.matchType equals `kittyKeyboard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Flush a query batch and receive DA1")
val querier = TerminalQuerier.new()
querier.send(decrqm(2026))
querier.flush()
querier.send(kittyKeyboard())
querier.onResponse(response("da1"))
expect(querier.resolved).to_equal(["decrpm:undefined", "sentinel:resolved"])
expect(querier.pendingCount()).to_equal(1)
expect(querier.queue[0].query.matchType).to_equal("kittyKeyboard")
```

</details>

#### should let explicit DA1 queries consume the first DA1 before sentinel

- Send explicit DA1 and then flush
- querier send
- querier flush
- querier onResponse
   - Expected: querier.resolved[0] equals `da1:da1`
   - Expected: querier.pendingCount() equals `1`
- querier onResponse
   - Expected: querier.resolved[1] equals `sentinel:resolved`
   - Expected: querier.pendingCount() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Send explicit DA1 and then flush")
val querier = TerminalQuerier.new()
querier.send(da1())
querier.flush()
querier.onResponse(response("da1"))
expect(querier.resolved[0]).to_equal("da1:da1")
expect(querier.pendingCount()).to_equal(1)
querier.onResponse(response("da1"))
expect(querier.resolved[1]).to_equal("sentinel:resolved")
expect(querier.pendingCount()).to_equal(0)
```

</details>

#### should ignore unsolicited non-sentinel responses

- Dispatch a response with no pending match
- querier onResponse
   - Expected: querier.resolved.len() equals `0`
   - Expected: querier.pendingCount() equals `0`
   - Expected: terminalQuerierSourceLinesModeled() equals `212`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a response with no pending match")
val querier = TerminalQuerier.new()
querier.onResponse(response("xtversion"))
expect(querier.resolved.len()).to_equal(0)
expect(querier.pendingCount()).to_equal(0)
expect(terminalQuerierSourceLinesModeled()).to_equal(212)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
