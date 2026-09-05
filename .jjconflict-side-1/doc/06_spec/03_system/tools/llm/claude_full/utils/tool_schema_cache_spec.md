# Claude Full tool schema cache

> Pure Simple coverage for session-scoped tool schema cache behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full tool schema cache

Pure Simple coverage for session-scoped tool schema cache behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/tool_schema_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for session-scoped tool schema cache behavior.

## Scenarios

### Claude full tool schema cache

#### stores and returns cached schemas

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores and returns cached schemas
- Check cache insert
   - Expected: entry.schema equals `{"type":"object"}`
   - Expected: entry.strict equals `Some(true)`
   - Expected: entry.eagerInputStreaming equals `Some(false)`
   - Expected: false is true
   - Expected: toolSchemaCacheSize("s1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores and returns cached schemas")
step("Check cache insert")
clearToolSchemaCache("s1")
putToolSchemaCache("s1", "Read", "{\"type\":\"object\"}", Some(true), Some(false))
val cached = getToolSchemaCache("s1", "Read")
if val entry = cached:
    expect(entry.schema).to_equal("{\"type\":\"object\"}")
    expect(entry.strict).to_equal(Some(true))
    expect(entry.eagerInputStreaming).to_equal(Some(false))
else:
    expect(false).to_equal(true)
expect(toolSchemaCacheSize("s1")).to_equal(1)
```

</details>

#### replaces cache entries by name

- replaces cache entries by name
- Check same-key replacement
   - Expected: entry.schema equals `new`
   - Expected: entry.strict equals `Some(true)`
   - Expected: entry.eagerInputStreaming equals `Some(true)`
   - Expected: false is true
   - Expected: toolSchemaCacheSize("s1") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replaces cache entries by name")
step("Check same-key replacement")
clearToolSchemaCache("s1")
putToolSchemaCache("s1", "Write", "old", Some(false), Some(false))
putToolSchemaCache("s1", "Write", "new", Some(true), Some(true))
val cached = getToolSchemaCache("s1", "Write")
if val entry = cached:
    expect(entry.schema).to_equal("new")
    expect(entry.strict).to_equal(Some(true))
    expect(entry.eagerInputStreaming).to_equal(Some(true))
else:
    expect(false).to_equal(true)
expect(toolSchemaCacheSize("s1")).to_equal(1)
```

</details>

#### preserves absent optional flags

- preserves absent optional flags
- Check absent flags
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves absent optional flags")
step("Check absent flags")
clearToolSchemaCache("s1")
putToolSchemaCache("s1", "Loose", "schema", nil, nil)
val cached = getToolSchemaCache("s1", "Loose")
if val entry = cached:
    expect(entry.strict).to_be_nil()
    expect(entry.eagerInputStreaming).to_be_nil()
else:
    expect(false).to_equal(true)
```

</details>

#### keeps sessions isolated

- keeps sessions isolated
- Check session partition
   - Expected: entry.schema equals `one`
   - Expected: false is true
   - Expected: entry.schema equals `two`
   - Expected: false is true
   - Expected: toolSchemaCacheSize("s1") equals `1`
   - Expected: toolSchemaCacheSize("s2") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps sessions isolated")
step("Check session partition")
clearToolSchemaCache("s1")
clearToolSchemaCache("s2")
putToolSchemaCache("s1", "Read", "one", nil, nil)
putToolSchemaCache("s2", "Read", "two", nil, nil)
val first = getToolSchemaCache("s1", "Read")
val second = getToolSchemaCache("s2", "Read")
if val entry = first:
    expect(entry.schema).to_equal("one")
else:
    expect(false).to_equal(true)
if val entry = second:
    expect(entry.schema).to_equal("two")
else:
    expect(false).to_equal(true)
expect(toolSchemaCacheSize("s1")).to_equal(1)
expect(toolSchemaCacheSize("s2")).to_equal(1)
```

</details>

#### returns nil for missing schema names

- returns nil for missing schema names
- Check cache miss


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for missing schema names")
step("Check cache miss")
clearToolSchemaCache("s1")
expect(getToolSchemaCache("s1", "Missing")).to_be_nil()
```

</details>

#### clears all cached schemas

- clears all cached schemas
- Check clear
   - Expected: entry.strict equals `Some(false)`
   - Expected: entry.eagerInputStreaming equals `Some(false)`
   - Expected: false is true
   - Expected: toolSchemaCacheSize("s1") equals `0`
   - Expected: toolSchemaCacheSize("s2") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears all cached schemas")
step("Check clear")
clearToolSchemaCache("s1")
clearToolSchemaCache("s2")
putToolSchemaCache("s1", "A", "a", nil, nil)
putToolSchemaCache("s1", "B", "b", Some(false), Some(false))
putToolSchemaCache("s2", "C", "c", nil, nil)
val beforeClear = getToolSchemaCache("s1", "B")
if val entry = beforeClear:
    expect(entry.strict).to_equal(Some(false))
    expect(entry.eagerInputStreaming).to_equal(Some(false))
else:
    expect(false).to_equal(true)
clearToolSchemaCache("s1")
expect(toolSchemaCacheSize("s1")).to_equal(0)
expect(toolSchemaCacheSize("s2")).to_equal(1)
expect(getToolSchemaCache("s1", "A")).to_be_nil()
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3da7f35e540397ba1569a560f95feb93220ec8ff465b23cb521db73195df5b05`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3da7f35e540397ba1569a560f95feb93220ec8ff465b23cb521db73195df5b05`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3da7f35e540397ba1569a560f95feb93220ec8ff465b23cb521db73195df5b05`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/tool_schema_cache_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/tool_schema_cache_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/tool_schema_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/tool_schema_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/tool_schema_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/tool_schema_cache_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores and returns cached schemas' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/tool_schema_cache_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces cache entries by name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/tool_schema_cache_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves absent optional flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
