# Web Contents Specification

> Tests covering WebContents.new, WebContents mutations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Contents Specification

## Scenarios

### WebContents.new

#### gives correct id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gives correct id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives correct id")
val wc = WebContents.new(42, _rect())
expect wc.id to_equal 42
```

</details>

#### gives correct viewport

- gives correct viewport


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives correct viewport")
val wc = WebContents.new(1, _rect())
expect wc.viewport.right to_equal 800.0
```

</details>

#### main_frame_surface has matching client_id

- main_frame_surface has matching client_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("main_frame_surface has matching client_id")
val wc = WebContents.new(7, _rect())
expect wc.main_frame_surface.frame_sink_id.client_id to_equal 7
```

</details>

#### main_frame_surface sink_id is 1

- main_frame_surface sink_id is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("main_frame_surface sink_id is 1")
val wc = WebContents.new(3, _rect())
expect wc.main_frame_surface.frame_sink_id.sink_id to_equal 1
```

</details>

### WebContents mutations

#### navigate updates url

- navigate updates url


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("navigate updates url")
var wc = WebContents.new(1, _rect())
wc.navigate("https://example.com")
expect wc.url to_equal "https://example.com"
```

</details>

#### set_title updates title

- set_title updates title


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_title updates title")
var wc = WebContents.new(1, _rect())
wc.set_title("Hello")
expect wc.title to_equal "Hello"
```

</details>

#### last_paint is empty before any paint

- last_paint is empty before any paint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("last_paint is empty before any paint")
val wc = WebContents.new(1, _rect())
val has_paint = wc.last_paint.is_some()
expect has_paint to_equal false
```

</details>

#### update_paint stores the artifact's own chunks, not an empty artifact

- update_paint stores the artifact's own chunks, not an empty artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("update_paint stores the artifact's own chunks, not an empty artifact")
var wc = WebContents.new(1, _rect())
val props = PaintChunkProperties.root()
val no_items: [DisplayItem] = []
val chunks = [
    PaintChunk.create(begin_index: 0, end_index: 3, properties: props),
    PaintChunk.create(begin_index: 3, end_index: 7, properties: props)
]
wc.update_paint(PaintArtifact.create(items: no_items, chunks: chunks))
# Sentinels stay at -1 if last_paint is None, so a missing store fails
# closed rather than skipping the assertions.
var chunk_count = -1
var last_end = -1
if val stored = wc.last_paint:
    chunk_count = stored.chunk_count()
    if stored.chunk_count() > 1:
        last_end = stored.chunks[1].end_index
expect chunk_count to_equal 2
expect last_end to_equal 7
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/content/web_contents_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WebContents.new, WebContents mutations.
- WebContents.new
- WebContents mutations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `6324df6257916fa8db591e6723ba99298662709424723196bdc5ad45edd573c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6324df6257916fa8db591e6723ba99298662709424723196bdc5ad45edd573c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6324df6257916fa8db591e6723ba99298662709424723196bdc5ad45edd573c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/content/web_contents_spec.spl
mirror: doc/06_spec/01_unit/lib/content/web_contents_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/content/web_contents_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/content/web_contents_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/content/web_contents_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives correct id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/content/web_contents_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives correct viewport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/content/web_contents_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'main_frame_surface has matching client_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
