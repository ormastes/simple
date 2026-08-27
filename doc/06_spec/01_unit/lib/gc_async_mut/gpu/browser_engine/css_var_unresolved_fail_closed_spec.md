# Css Var Unresolved Fail Closed Specification

> Tests covering css var: undefined property is fail-closed, not spliced empty, css var: a DEFINED property still resolves, css var: an explicit fallback still wins over the source text.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Css Var Unresolved Fail Closed Specification

## Scenarios

### css var: undefined property is fail-closed, not spliced empty

#### keeps the var() source text when the property is undefined

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the var() source text when the property is undefined


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the var() source text when the property is undefined")
val layers = probe(DECLS, "background_layers_raw")
expect(layers.contains("var(--app-surface)")).to_be_true()
```

</details>

#### does not emit the bare trailing comma that the old splice produced

- does not emit the bare trailing comma that the old splice produced


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not emit the bare trailing comma that the old splice produced")
val layers = probe(DECLS, "background_layers_raw")
expect(layers.ends_with(",")).to_be_false()
```

</details>

#### keeps the blur var() so the backdrop term is not degraded to blur()

- keeps the blur var() so the backdrop term is not degraded to blur()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the blur var() so the backdrop term is not degraded to blur()")
val backdrop = probe(DECLS, "backdrop_filter_raw")
expect(backdrop.contains("blur(var(--blur-surface))")).to_be_true()
```

</details>

#### does not produce the degraded `blur()` term

- does not produce the degraded `blur()` term


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not produce the degraded `blur()` term")
val backdrop = probe(DECLS, "backdrop_filter_raw")
expect(backdrop.contains("blur()")).to_be_false()
```

</details>

### css var: a DEFINED property still resolves

#### substitutes the surface colour when :root is in scope

- substitutes the surface colour when :root is in scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("substitutes the surface colour when :root is in scope")
val layers = probe(ROOT + DECLS, "background_layers_raw")
expect(layers.contains("rgba(31,31,33,0.80)")).to_be_true()
```

</details>

#### leaves no literal var() behind when :root is in scope

- leaves no literal var() behind when :root is in scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves no literal var() behind when :root is in scope")
val layers = probe(ROOT + DECLS, "background_layers_raw")
expect(layers.contains("var(")).to_be_false()
```

</details>

#### resolves the blur length to a px term

- resolves the blur length to a px term


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the blur length to a px term")
val backdrop = probe(ROOT + DECLS, "backdrop_filter_raw")
expect(backdrop.contains("blur(30px)")).to_be_true()
```

</details>

### css var: an explicit fallback still wins over the source text

#### uses the fallback for an undefined property

- uses the fallback for an undefined property


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the fallback for an undefined property")
val layers = probe(
    "#t{background: linear-gradient(180deg, rgba(9,9,9,0.1), " +
    "rgba(8,8,8,0.2)), var(--missing, rgba(1,2,3,0.5));}",
    "background_layers_raw"
)
expect(layers.contains("rgba(1,2,3,0.5)")).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_var_unresolved_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering css var: undefined property is fail-closed, not spliced empty, css var: a DEFINED property still resolves, css var: an explicit fallback still wins over the source text.
- css var: undefined property is fail-closed, not spliced empty
- css var: a DEFINED property still resolves
- css var: an explicit fallback still wins over the source text

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

- Canonical SPipe generation for source `4b5460fe49f46eda09b302a145099404ad440d2b0db80dbf5804ee6e0d3eca77`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b5460fe49f46eda09b302a145099404ad440d2b0db80dbf5804ee6e0d3eca77`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b5460fe49f46eda09b302a145099404ad440d2b0db80dbf5804ee6e0d3eca77`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_var_unresolved_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_var_unresolved_fail_closed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_var_unresolved_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_var_unresolved_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_var_unresolved_fail_closed_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the var() source text when the property is undefined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_var_unresolved_fail_closed_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not emit the bare trailing comma that the old splice produced' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_var_unresolved_fail_closed_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the blur var() so the backdrop term is not degraded to blur()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
