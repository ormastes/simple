# Aspect facet model and completeness seal

> The typed facet/advice/pointcut model (§13.3) plus the binding completeness check and the seal it freezes (§13.4, §13.5).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aspect facet model and completeness seal

The typed facet/advice/pointcut model (§13.3) plus the binding completeness check and the seal it freezes (§13.4, §13.5).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / Semantics / Aspect seal |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/aspect_seal/aspect_seal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The typed facet/advice/pointcut model (§13.3) plus the binding completeness
check and the seal it freezes (§13.4, §13.5).

Covered:
- a clean aspect document seals, and the seal hash is order-independent
- a required facet bound zero times is `E-ASPECT-001`
- a facet bound twice is `E-ASPECT-002`
- `late` activation under a critical profile is `E-ASPECT-003`, and is
  admitted under a non-critical profile
- an aspect demanding verified provenance is ALWAYS refused with
  `E-ASPECT-004` "not verified" — no verifier and no authority is wired
- an `open_dyn_patchpoint` advice mode is not critical-safe (§13.6)
- the post-weave recheck is a stub that re-runs binding completeness and
  re-derives the hash; it proves self-consistency, not weaving

## Scenarios

### aspect seal — happy path

#### parses the clean fixture into a typed model

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the clean fixture into a typed model


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the clean fixture into a typed model")
val set = load("audit_trace_clean.sdn")
assert_equal(set.aspects.len(), 1)
assert_equal(set.aspects[0].id, "audit.trace")
assert_equal(set.aspects[0].facets.len(), 2)
assert_equal(set.aspects[0].advice.len(), 2)
assert_equal(set.bindings.len(), 2)
```

</details>

#### seals a complete, unique binding set under a critical profile

- seals a complete, unique binding set under a critical profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seals a complete, unique binding set under a critical profile")
match aspect_seal_check(load("audit_trace_clean.sdn"), AspectSealProfile(critical: true)):
    case Ok(s):
        assert_true(s.profile_critical)
        assert_equal(s.aspect_ids.len(), 1)
        assert_equal(s.binding_count, 2)
        assert_equal(s.obligation_count, 2)
        assert_true(s.seal_hash.starts_with("ASPECTSEALV1-"))
        assert_equal(s.advice_order.len(), 2)
    case Err(reasons):
        assert_equal(reasons.len(), 0)
```

</details>

#### carries the signature blob as NOT VERIFIED rather than checking it

- carries the signature blob as NOT VERIFIED rather than checking it


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries the signature blob as NOT VERIFIED rather than checking it")
match aspect_seal_check(load("audit_trace_clean.sdn"), AspectSealProfile(critical: true)):
    case Ok(s):
        assert_equal(s.unverified_signatures.len(), 1)
        assert_true(s.unverified_signatures[0].contains("NOT VERIFIED"))
    case Err(_):
        assert_true(false)
```

</details>

### aspect seal — deterministic hash

#### hashes the same set identically regardless of binding order

- hashes the same set identically regardless of binding order


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes the same set identically regardless of binding order")
val set = load("audit_trace_clean.sdn")
val reversed = AspectBindingSet(
    aspects: set.aspects,
    bindings: [set.bindings[1], set.bindings[0]]
)
assert_equal(
    binding_set_hash(set, "profile=critical"),
    binding_set_hash(reversed, "profile=critical")
)
```

</details>

#### separates profiles and reacts to any binding change

- separates profiles and reacts to any binding change


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates profiles and reacts to any binding change")
val set = load("audit_trace_clean.sdn")
assert_true(binding_set_hash(set, "profile=critical")
    != binding_set_hash(set, "profile=default"))
val changed = AspectBindingSet(
    aspects: set.aspects,
    bindings: set.bindings + [FacetBinding(
        aspect_id: "audit.trace",
        facet: "Extra",
        concrete_type: "T",
        handler: "h",
        activation: "startup"
    )]
)
assert_true(binding_set_hash(set, "profile=critical")
    != binding_set_hash(changed, "profile=critical"))
```

</details>

#### sorts the canonical lines it hashes

- sorts the canonical lines it hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts the canonical lines it hashes")
val lines = canonical_lines(load("audit_trace_clean.sdn"))
assert_equal(lines.len(), 5)
var i: i64 = 1
while i < lines.len():
    assert_true(lines[i - 1] <= lines[i])
    i = i + 1
```

</details>

### aspect seal — closed rejection reasons

#### rejects a required facet bound zero times

- rejects a required facet bound zero times


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a required facet bound zero times")
val codes = codes_of("unbound_required.sdn", true)
assert_true(contains(codes, "E-ASPECT-001"))
```

</details>

#### rejects a facet bound more than once

- rejects a facet bound more than once


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a facet bound more than once")
val codes = codes_of("duplicate_binding.sdn", true)
assert_true(contains(codes, "E-ASPECT-002"))
```

</details>

#### rejects late activation under a critical profile

- rejects late activation under a critical profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects late activation under a critical profile")
val codes = codes_of("late_activation.sdn", true)
assert_true(contains(codes, "E-ASPECT-003"))
```

</details>

#### admits late activation when the profile is not critical

- admits late activation when the profile is not critical


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits late activation when the profile is not critical")
val codes = codes_of("late_activation.sdn", false)
assert_equal(codes.len(), 0)
```

</details>

#### names the unbound facet's required interface in the diagnostic

- names the unbound facet's required interface in the diagnostic


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the unbound facet's required interface in the diagnostic")
match aspect_seal_check(load("unbound_required.sdn"), AspectSealProfile(critical: true)):
    case Ok(_):
        assert_true(false)
    case Err(reasons):
        var found = false
        for r in reasons:
            if aspect_seal_reason_code(r) == "E-ASPECT-001":
                assert_true(aspect_seal_reason_text(r).contains("TraceFacet"))
                found = true
        assert_true(found)
```

</details>

### aspect seal — signatures are never enforced

#### always refuses an aspect that demands verified provenance

- always refuses an aspect that demands verified provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("always refuses an aspect that demands verified provenance")
val codes = codes_of("signature_required.sdn", true)
assert_true(contains(codes, "E-ASPECT-004"))
```

</details>

#### says NOT VERIFIED instead of claiming a verification result

- says NOT VERIFIED instead of claiming a verification result


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("says NOT VERIFIED instead of claiming a verification result")
match aspect_seal_check(load("signature_required.sdn"), AspectSealProfile(critical: true)):
    case Ok(_):
        assert_true(false)
    case Err(reasons):
        var found = false
        for r in reasons:
            if aspect_seal_reason_code(r) == "E-ASPECT-004":
                assert_true(aspect_seal_reason_text(r).contains("NOT VERIFIED"))
                found = true
        assert_true(found)
```

</details>

#### refuses it under a non-critical profile too

- refuses it under a non-critical profile too


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses it under a non-critical profile too")
val codes = codes_of("signature_required.sdn", false)
assert_true(contains(codes, "E-ASPECT-004"))
```

</details>

### aspect seal — advice modes (§13.6)

#### classifies every closed mode's critical safety

- classifies every closed mode's critical safety


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies every closed mode's critical safety")
match advice_mode_from_text("open_dyn_patchpoint"):
    case Some(m): assert_true(not advice_mode_critical_safe(m))
    case None: assert_true(false)
match advice_mode_from_text("static_weave"):
    case Some(m): assert_true(advice_mode_critical_safe(m))
    case None: assert_true(false)
```

</details>

#### has no mode outside the closed set

- has no mode outside the closed set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no mode outside the closed set")
match advice_mode_from_text("hot_reweave"):
    case Some(_): assert_true(false)
    case None: assert_true(true)
```

</details>

#### reports an open dyn patchpoint under a critical profile

- reports an open dyn patchpoint under a critical profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an open dyn patchpoint under a critical profile")
val set = AspectBindingSet(
    aspects: [AspectDecl(
        id: "a.dyn",
        version: 1,
        provider_module: "m",
        activation: "startup",
        signature: "",
        signature_authority: "",
        signature_required: false,
        facets: [FacetDecl(facet: "F", interface_name: "IF", required: true)],
        advice: [AdviceDecl(
            name: "adv",
            mode: "open_dyn_patchpoint",
            order: 1,
            pointcut: Pointcut(expr: "call(*)", matched: ["jp:1"])
        )]
    )],
    bindings: [FacetBinding(
        aspect_id: "a.dyn",
        facet: "F",
        concrete_type: "T",
        handler: "h",
        activation: "startup"
    )]
)
val report = binding_completeness(set, true)
assert_equal(report.open_dyn_advice.len(), 1)
assert_equal(binding_completeness(set, false).open_dyn_advice.len(), 0)
```

</details>

### aspect seal — post-weave recheck is a stub

#### runs over the sealed set and is stable

- runs over the sealed set and is stable


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs over the sealed set and is stable")
val set = load("audit_trace_clean.sdn")
val profile = AspectSealProfile(critical: true)
match aspect_seal_check(set, profile):
    case Ok(s):
        # STUB: re-runs binding_completeness and re-derives the hash.
        # It does NOT re-verify woven HIR — no weaver is wired.
        assert_true(post_weave_recheck(s, set, profile))
    case Err(_):
        assert_true(false)
```

</details>

#### reports false when the set drifts away from the sealed hash

- reports false when the set drifts away from the sealed hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports false when the set drifts away from the sealed hash")
val set = load("audit_trace_clean.sdn")
val profile = AspectSealProfile(critical: true)
match aspect_seal_check(set, profile):
    case Ok(s):
        val drifted = AspectBindingSet(
            aspects: set.aspects,
            bindings: [set.bindings[0]]
        )
        assert_true(not post_weave_recheck(s, drifted, profile))
    case Err(_):
        assert_true(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `8788409f8106217b0a695b3180c65d7c13555ffec2be6877760a6dc20e8eb965`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8788409f8106217b0a695b3180c65d7c13555ffec2be6877760a6dc20e8eb965`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8788409f8106217b0a695b3180c65d7c13555ffec2be6877760a6dc20e8eb965`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/aspect_seal/aspect_seal_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/aspect_seal/aspect_seal_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/aspect_seal/aspect_seal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/aspect_seal/aspect_seal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/aspect_seal/aspect_seal_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the clean fixture into a typed model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/aspect_seal/aspect_seal_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seals a complete, unique binding set under a critical profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/aspect_seal/aspect_seal_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries the signature blob as NOT VERIFIED rather than checking it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
