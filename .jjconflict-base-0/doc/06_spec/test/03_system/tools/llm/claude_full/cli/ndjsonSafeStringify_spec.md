# Claude Full CLI NDJSON Safe Stringify

> Checks escaping for JavaScript line terminators in one-line JSON output.

<!-- sdn-diagram:id=ndjsonSafeStringify_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndjsonSafeStringify_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndjsonSafeStringify_spec -> std
ndjsonSafeStringify_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndjsonSafeStringify_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI NDJSON Safe Stringify

Checks escaping for JavaScript line terminators in one-line JSON output.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/ndjsonSafeStringify_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks escaping for JavaScript line terminators in one-line JSON output.

## Scenarios

### Claude full cli ndjson safe stringify

#### escapes JavaScript line terminators

- Line and paragraph separators become slash-u escapes
   - Expected: escaped equals `{"text":"a\\u2028b\\u2029c"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Line and paragraph separators become slash-u escapes")
val json = "{\"text\":\"a" + lineSeparatorChar() + "b" + paragraphSeparatorChar() + "c\"}"
val escaped = ndjsonSafeStringify(json)
expect(escaped).to_equal("{\"text\":\"a\\u2028b\\u2029c\"}")
```

</details>

#### leaves ordinary JSON unchanged

- Normal one-line JSON remains stable
   - Expected: escapeJsLineTerminators("{\"ok\":true}") equals `{"ok":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Normal one-line JSON remains stable")
expect(escapeJsLineTerminators("{\"ok\":true}")).to_equal("{\"ok\":true}")
```

</details>

#### exports source-backed constants

- Pin the transport-safety contract
   - Expected: escapedLineSeparator() equals `\\u2028`
   - Expected: escapedParagraphSeparator() equals `\\u2029`
   - Expected: jsLineTerminatorsPattern() equals `\\u2028|\\u2029`
   - Expected: usesSingleAlternationRegexInSource() is true
   - Expected: preservesJsonParseValue() is true
   - Expected: protectsOneMessagePerLineTransports() is true
   - Expected: ndjsonSafeStringifySourceLinesModeled() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin the transport-safety contract")
expect(escapedLineSeparator()).to_equal("\\u2028")
expect(escapedParagraphSeparator()).to_equal("\\u2029")
expect(jsLineTerminatorsPattern()).to_equal("\\u2028|\\u2029")
expect(usesSingleAlternationRegexInSource()).to_equal(true)
expect(preservesJsonParseValue()).to_equal(true)
expect(protectsOneMessagePerLineTransports()).to_equal(true)
expect(ndjsonSafeStringifySourceLinesModeled()).to_equal(32)
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
