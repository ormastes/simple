# Lazy Outline Equivalence

> Outline path: collect top-level declaration names from col-0 lines only.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lazy Outline Equivalence

Outline path: collect top-level declaration names from col-0 lines only.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/lazy_outline_equivalence/lazy_outline_equivalence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Outline path: collect top-level declaration names from col-0 lines only.
    Mimics treesitter fast_mode: function bodies (indented lines) are skipped.

## Scenarios

### Lazy Outline Equivalence

#### graph.spl — ImportGraph + cycle detection

#### outline and full parse yield same declaration surface

- outline and full parse yield same declaration surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline and full parse yield same declaration surface")
check(check_equiv(graph_src, "graph.spl"))
```

</details>

#### outline is non-empty

- outline is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline is non-empty")
check(check_nonempty(graph_src, "graph.spl"))
```

</details>

#### ImportGraph struct is in outline surface

- ImportGraph struct is in outline surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ImportGraph struct is in outline surface")
check(check_name_present(graph_src, "ImportGraph"))
```

</details>

#### ImportKind enum is in outline surface

- ImportKind enum is in outline surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ImportKind enum is in outline surface")
check(check_name_present(graph_src, "ImportKind"))
```

</details>

#### importgraph_add_edge fn is in outline surface

- importgraph_add_edge fn is in outline surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("importgraph_add_edge fn is in outline surface")
check(check_name_present(graph_src, "importgraph_add_edge"))
```

</details>

#### importgraph_find_cycles fn is in outline surface

- importgraph_find_cycles fn is in outline surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("importgraph_find_cycles fn is in outline surface")
check(check_name_present(graph_src, "importgraph_find_cycles"))
```

</details>

#### markdown/types.spl — struct/enum declarations

#### outline and full parse yield same declaration surface

- outline and full parse yield same declaration surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline and full parse yield same declaration surface")
check(check_equiv(md_types_src, "markdown/types.spl"))
```

</details>

#### outline is non-empty

- outline is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline is non-empty")
check(check_nonempty(md_types_src, "markdown/types.spl"))
```

</details>

#### cbor/types.spl — struct/enum/fn module

#### outline and full parse yield same declaration surface

- outline and full parse yield same declaration surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline and full parse yield same declaration surface")
check(check_equiv(cbor_types_src, "cbor/types.spl"))
```

</details>

#### outline is non-empty

- outline is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline is non-empty")
check(check_nonempty(cbor_types_src, "cbor/types.spl"))
```

</details>

#### cbor/utilities.spl — fn-heavy module

#### outline and full parse yield same declaration surface

- outline and full parse yield same declaration surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline and full parse yield same declaration surface")
check(check_equiv(cbor_util_src, "cbor/utilities.spl"))
```

</details>

#### outline is non-empty

- outline is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline is non-empty")
check(check_nonempty(cbor_util_src, "cbor/utilities.spl"))
```

</details>

#### ui/color.spl — struct + fn module

#### outline and full parse yield same declaration surface

- outline and full parse yield same declaration surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline and full parse yield same declaration surface")
check(check_equiv(color_src, "ui/color.spl"))
```

</details>

#### outline is non-empty

- outline is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outline is non-empty")
check(check_nonempty(color_src, "ui/color.spl"))
```

</details>

#### indent-fence invariant

#### body lines (indented) are never collected by outline scanner

- body lines (indented) are never collected by outline scanner


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("body lines (indented) are never collected by outline scanner")
# Synthetic source: fn with indented body that contains a nested fn keyword
val src = "fn outer():\n    fn inner_not_decl():\n        pass\nstruct Foo:\n    x: i64\n"
val names = scan_outline(src)
# inner_not_decl should NOT appear (indented)
var found_inner = false
for n in names:
    if n.contains("inner_not_decl"):
        found_inner = true
check(not found_inner)
# outer and Foo SHOULD appear
check(check_name_present(src, "outer"))
check(check_name_present(src, "Foo"))
```

</details>

#### export-qualified fns are captured by outline scanner

- export-qualified fns are captured by outline scanner


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("export-qualified fns are captured by outline scanner")
val src = "export fn my_fn(x: i64) -> i64:\n    x + 1\nfn other():\n    pass\n"
check(check_name_present(src, "my_fn"))
check(check_name_present(src, "other"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `3f21b5278734e256ff977eaa63a8cf15d8288ab0add8d2499b859f9429f235ed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f21b5278734e256ff977eaa63a8cf15d8288ab0add8d2499b859f9429f235ed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f21b5278734e256ff977eaa63a8cf15d8288ab0add8d2499b859f9429f235ed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/lazy_outline_equivalence/lazy_outline_equivalence_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/lazy_outline_equivalence/lazy_outline_equivalence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/lazy_outline_equivalence/lazy_outline_equivalence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/lazy_outline_equivalence/lazy_outline_equivalence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/lazy_outline_equivalence/lazy_outline_equivalence_spec.spl:258:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'outline and full parse yield same declaration surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/lazy_outline_equivalence/lazy_outline_equivalence_spec.spl:263:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'outline is non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/lazy_outline_equivalence/lazy_outline_equivalence_spec.spl:268:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ImportGraph struct is in outline surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
