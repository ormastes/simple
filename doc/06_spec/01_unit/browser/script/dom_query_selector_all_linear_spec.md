# Linear DOM querySelectorAll

> Proves querySelectorAll keeps preorder document order without recursive

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linear DOM querySelectorAll

Proves querySelectorAll keeps preorder document order without recursive

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/dom_query_selector_all_linear_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves querySelectorAll keeps preorder document order without recursive
per-subtree result arrays. This is source and semantic evidence only; it does
not claim production timing or RSS evidence.

## Scenarios

### DOM querySelectorAll linear traversal

#### uses one iterative preorder traversal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses one iterative preorder traversal
- Inspect the querySelectorAll traversal owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER
step("uses one iterative preorder traversal")
step("Inspect the querySelectorAll traversal owner")
val source = read_file_text(
    "src/lib/gc_async_mut/gpu/browser_engine/script/dom_api.spl"
) ?? ""
expect(source).to_contain("var stack: [BeDomNode] = [root]")
expect(source).to_contain("val node = stack.pop()")
expect(source.contains(
    "document_query_selector_all(root.children[i], sel)"
)).to_equal(false)
expect(source.contains(
    "val child_matches = document_query_selector_all"
)).to_equal(false)
```

</details>

#### preserves exact order for 512 siblings

- preserves exact order for 512 siblings
- Build 512 matching siblings in document order
- Query every matching sibling once
   - Expected: matches.len() equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER
step("preserves exact order for 512 siblings")
step("Build 512 matching siblings in document order")
var root = document_create_element("div")
var i = 0
while i < 512:
    root = node_append_child(root, _query_node(i.to_text()))
    i = i + 1

step("Query every matching sibling once")
val matches = document_query_selector_all(root, "p")
expect(matches.len()).to_equal(512)
i = 0
while i < matches.len():
    expect(node_get_attribute(matches[i], "id") ?? "").to_equal(
        i.to_text()
    )
    i = i + 1
```

</details>

#### preserves preorder across a deep chain and siblings

- preserves preorder across a deep chain and siblings
- Build a 64-level chain with a preceding sibling at each level
- Query the mixed tree in preorder
   - Expected: matches.len() equals `127`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER
step("preserves preorder across a deep chain and siblings")
step("Build a 64-level chain with a preceding sibling at each level")
var chain = _query_node("deep-63")
var depth = 62
while depth >= 0:
    var parent = _query_node("deep-" + depth.to_text())
    parent = node_append_child(
        parent, _query_node("side-" + depth.to_text())
    )
    parent = node_append_child(parent, chain)
    chain = parent
    depth = depth - 1

step("Query the mixed tree in preorder")
val matches = document_query_selector_all(chain, "p")
expect(matches.len()).to_equal(127)
depth = 0
var match_i = 0
while depth < 63:
    expect(node_get_attribute(
        matches[match_i], "id"
    ) ?? "").to_equal("deep-" + depth.to_text())
    expect(node_get_attribute(
        matches[match_i + 1], "id"
    ) ?? "").to_equal("side-" + depth.to_text())
    depth = depth + 1
    match_i = match_i + 2
expect(node_get_attribute(
    matches[126], "id"
) ?? "").to_equal("deep-63")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `70753e1c41813c96128a306306117770354329bf9643b1376281aae83f780a0e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70753e1c41813c96128a306306117770354329bf9643b1376281aae83f780a0e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70753e1c41813c96128a306306117770354329bf9643b1376281aae83f780a0e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/browser/script/dom_query_selector_all_linear_spec.spl
mirror: doc/06_spec/01_unit/browser/script/dom_query_selector_all_linear_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=30
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/browser/script/dom_query_selector_all_linear_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser/script/dom_query_selector_all_linear_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser/script/dom_query_selector_all_linear_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/browser/script/dom_query_selector_all_linear_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser/script/dom_query_selector_all_linear_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses one iterative preorder traversal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser/script/dom_query_selector_all_linear_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves exact order for 512 siblings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser/script/dom_query_selector_all_linear_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves preorder across a deep chain and siblings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
