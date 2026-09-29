# w0_property_id_declarations_spec

> Purpose: Prove that W0 PropertyId + Declaration + apply_declarations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# w0_property_id_declarations_spec

Purpose: Prove that W0 PropertyId + Declaration + apply_declarations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that W0 PropertyId + Declaration + apply_declarations.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### W0 PropertyId + Declaration + apply_declarations

#### parses each known CSS property name to a distinct, stable PropertyId

- parses each known CSS property name to a distinct, stable PropertyId
- Verify: parses each known CSS property name to a distinct, stable PropertyId
   - Expected: property_id_from_name("display") equals `PROPERTY_ID_DISPLAY`
   - Expected: property_id_from_name("not-a-real-property") equals `PROPERTY_ID_UNKNOWN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses each known CSS property name to a distinct, stable PropertyId")
step("Verify: parses each known CSS property name to a distinct, stable PropertyId")
# @req: REQ-LIB-GC-ASYNC-MUT-001
expect(property_id_from_name("display")).to_equal(PROPERTY_ID_DISPLAY)
expect(property_id_from_name("not-a-real-property")).to_equal(PROPERTY_ID_UNKNOWN)
```

</details>

#### applies all 11 known-property declarations and writes the correct typed hot field each

- applies all 11 known-property declarations and writes the correct typed hot field each
- Verify: applies all 11 known-property declarations and writes the correct typed hot field each
   - Expected: hot.display equals `flex`
   - Expected: hot.opacity_pct equals `50`
   - Expected: hot.fg equals `0x112233FFu32`
   - Expected: hot.width_px equals `100`
   - Expected: hot.height_px equals `50`
   - Expected: hot.z_index equals `-3`
   - Expected: stats["touched"] equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies all 11 known-property declarations and writes the correct typed hot field each")
step("Verify: applies all 11 known-property declarations and writes the correct typed hot field each")
var stats: Dict<text, i64> = {}
val decls: [Declaration] = [
    declaration_from_name_value("display", "flex", false),
    declaration_from_name_value("position", "absolute", false),
    declaration_from_name_value("visibility", "hidden", false),
    declaration_from_name_value("content-visibility", "hidden", false),
    declaration_from_name_value("opacity", "0.5", false),
    declaration_from_name_value("color", "#112233", false),
    declaration_from_name_value("width", "100px", false),
    declaration_from_name_value("height", "50px", false),
    declaration_from_name_value("box-sizing", "border-box", false),
    declaration_from_name_value("overflow", "hidden", false),
    declaration_from_name_value("z-index", "-3", false),
]
val hot = apply_declarations(fresh_hot(), decls, stats)

expect(hot.display).to_equal("flex")
assert_true(hot.position_absolute)
expect_not(hot.position_relative)
expect_not(hot.position_sticky)
expect_not(hot.position_fixed)
assert_true(hot.visibility_hidden)
assert_true(hot.content_visibility_hidden)
expect(hot.opacity_pct).to_equal(50)  # oracle: 50 — named expected value from the requirement
expect(hot.fg).to_equal(0x112233FFu32)
expect(hot.width_px).to_equal(100)  # oracle: 100 — named expected value from the requirement
expect(hot.height_px).to_equal(50)  # oracle: 50 — named expected value from the requirement
assert_true(hot.border_box)
assert_true(hot.overflow_hidden)
expect(hot.z_index).to_equal(-3)  # oracle: -3 — named expected value from the requirement

# Proportionality: exactly 11 declarations were applied — one touch
# per known-property declaration, not per ComputedStyleHot field
# examined and not tied to PROPERTY_ID_COUNT.
expect(stats["touched"]).to_equal(11)
```

</details>

#### proportionality: k known + m unknown declarations touch exactly k, never k+m and never PROPERTY_ID_COUNT

- proportionality: k known + m unknown declarations touch exactly k, never k+m and never PROPERTY_ID_COUNT
- Verify: proportionality: k known + m unknown declarations touch exactly k, never k+m and never PROPERTY_ID_COUNT
   - Expected: hot.display equals `block`
   - Expected: hot.opacity_pct equals `100`
   - Expected: hot.z_index equals `7`
   - Expected: stats["touched"] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("proportionality: k known + m unknown declarations touch exactly k, never k+m and never PROPERTY_ID_COUNT")
step("Verify: proportionality: k known + m unknown declarations touch exactly k, never k+m and never PROPERTY_ID_COUNT")
var stats: Dict<text, i64> = {}
val decls: [Declaration] = [
    declaration_from_name_value("display", "block", false),
    declaration_from_name_value("opacity", "1", false),
    declaration_from_name_value("z-index", "7", false),
    declaration_from_name_value("--custom-prop", "42", false),
    declaration_from_name_value("grid-template-columns", "1fr 1fr", false),
    declaration_from_name_value("transform", "rotate(3deg)", false),
    declaration_from_name_value("mask-image", "url(x.png)", false),
]
val hot = apply_declarations(fresh_hot(), decls, stats)
expect(hot.display).to_equal("block")
expect(hot.opacity_pct).to_equal(100)  # oracle: 100 — named expected value from the requirement
expect(hot.z_index).to_equal(7)  # oracle: 7 — named expected value from the requirement
# k = 3 known-property declarations; m = 4 unknown. Touch count must
# be exactly k = 3, distinguishing real O(k)-in-known-decls work
# from a design that would (wrongly) count every declaration seen
# (k+m = 7) or every property slot that exists (PROPERTY_ID_COUNT).
expect(stats["touched"]).to_equal(3)
```

</details>

#### an empty declaration list touches nothing and leaves the hot struct untouched

- an empty declaration list touches nothing and leaves the hot struct untouched
- Verify: an empty declaration list touches nothing and leaves the hot struct untouched
   - Expected: stats["touched"] equals `0`
   - Expected: hot.display equals `base.display`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an empty declaration list touches nothing and leaves the hot struct untouched")
step("Verify: an empty declaration list touches nothing and leaves the hot struct untouched")
var stats: Dict<text, i64> = {}
val base = fresh_hot()
val decls: [Declaration] = []
val hot = apply_declarations(base, decls, stats)
expect(stats["touched"]).to_equal(0)
expect(hot.display).to_equal(base.display)
```

</details>

#### growing the known-declaration count by 1 grows the touch count by exactly 1 (linear witness)

- growing the known-declaration count by 1 grows the touch count by exactly 1 (linear witness)
- Verify: growing the known-declaration count by 1 grows the touch count by exactly 1 (linear witness)
   - Expected: stats_a["touched"] equals `2`
   - Expected: stats_b["touched"] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("growing the known-declaration count by 1 grows the touch count by exactly 1 (linear witness)")
step("Verify: growing the known-declaration count by 1 grows the touch count by exactly 1 (linear witness)")
var stats_a: Dict<text, i64> = {}
val decls_a: [Declaration] = [
    declaration_from_name_value("display", "block", false),
    declaration_from_name_value("opacity", "1", false),
]
apply_declarations(fresh_hot(), decls_a, stats_a)
expect(stats_a["touched"]).to_equal(2)

var stats_b: Dict<text, i64> = {}
val decls_b: [Declaration] = [
    declaration_from_name_value("display", "block", false),
    declaration_from_name_value("opacity", "1", false),
    declaration_from_name_value("width", "10px", false),
]
apply_declarations(fresh_hot(), decls_b, stats_b)
expect(stats_b["touched"]).to_equal(3)
```

</details>

#### T1: the real style_block cascade reaches apply_declarations, not just style_property_id's own unit tests

- T1: the real style_block cascade reaches apply_declarations, not just style_property_id's own unit tests
- Verify: T1: the real style_block cascade reaches apply_declarations, not just style_property_id's own unit tests
   - Expected: stats["touched"] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("T1: the real style_block cascade reaches apply_declarations, not just style_property_id's own unit tests")
step("Verify: T1: the real style_block cascade reaches apply_declarations, not just style_property_id's own unit tests")
# W0 (apply_declarations et al.) was landed orphaned -- referenced by
# zero src/ importers per the plan's §1 W0 row. This proves
# style_block.spl's live cascade (apply_css_rules_to_tree_with_w0_stats
# shares its recursive path with the production
# apply_css_rules_to_tree entrypoint -- see style_block.spl) actually
# calls apply_declarations for every matched declaration with a known
# PropertyId, threading a real counter rather than a test-only stub.
val root = el("div", "target")
val rules: [CssRule] = [
    one_rule("#target", "display", "flex"),
    one_rule("#target", "color", "#112233"),
    one_rule("#target", "not-a-real-property", "x"),
]
var stats: Dict<text, i64> = {}
apply_css_rules_to_tree_with_w0_stats(root, rules, stats)
# 2 known-PropertyId declarations (display, color) matched #target;
# the unknown property must not count. This is the SAME
# proportionality contract as apply_declarations' own unit tests
# above, now proven reachable through the real selector-matched
# cascade instead of a hand-built Declaration list.
expect(stats["touched"]).to_equal(2)
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

- `REQ-SSPEC-LIB`
- `REQ-LIB-GC-ASYNC-MUT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `48951916ec23bb21c914a7c31a7d0ee19ca32d6d9f11aaac6671a7320ee6e6fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48951916ec23bb21c914a7c31a7d0ee19ca32d6d9f11aaac6671a7320ee6e6fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48951916ec23bb21c914a7c31a7d0ee19ca32d6d9f11aaac6671a7320ee6e6fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses each known CSS property name to a distinct, stable PropertyId' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies all 11 known-property declarations and writes the correct typed hot field each' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/w0_property_id_declarations_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'proportionality: k known + m unknown declarations touch exactly k, never k+m and never PROPERTY_ID_COUNT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
