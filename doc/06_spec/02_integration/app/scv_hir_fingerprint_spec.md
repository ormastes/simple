# scv_hir_fingerprint_spec

> Purpose: This spec proves SCV's interface / HIR fingerprints

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_hir_fingerprint_spec

Purpose: This spec proves SCV's interface / HIR fingerprints

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_hir_fingerprint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV's interface / HIR fingerprints
(SCV-IMPL-G-05): `syntactic_interface_id` is the Simple compiler frontend's
canonical `simple/compile-interface/v1` digest (compiler.semantics.interface
.compile_interface — reused, not reinvented) computed over the public
declaration surface the `simple` query pack extracts; `normalized_impl_hash`
is the compiler's comment/format-insensitive implementation digest; and the
fingerprint record STATES ITS GUARANTEE — a typed-HIR hash is reported as
unavailable rather than faked, because the compiler frontend has no typed-HIR
extractor yet. Discriminating properties: a body-only change keeps the
interface id and changes the impl hash; a comment-only change keeps both; a
signature change changes the interface id.
Audience: Maintainers of the SCV gates / build-invalidation layer.

## Scenarios

### scv interface and HIR fingerprints

#### reuses the compiler frontend's canonical compile-interface digest

**Manual warnings:**
- invalid manual visibility metadata: # @manual SCV commit gates (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-HIR-FINGERPRINT-001
# @req REQ-SSPEC-INTEGRATION
step "the fingerprint format names its version and the digest domain it wraps"
assert_equal(scv_hir_fingerprint_version(), "scv/hir-fingerprint/v1")
step "the syntactic interface id equals compile_interface_digest over the same surface built by hand"
var s = ApiSurface.create("m")
s.add_function(_sig("alpha", "x", "i64", "i64"))
s.add_function(_sig("beta", "x", "text", "bool"))
assert_equal(scv_syntactic_interface_id("m", SRC), "siface1:" + compile_interface_digest(s))
```

</details>

#### body-only and comment-only changes keep the interface id; a signature change does not

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-HIR-FINGERPRINT-001
val base = scv_syntactic_interface_id("m", SRC)
step "body-only change: same interface id, different normalized impl hash"
assert_equal(scv_syntactic_interface_id("m", SRC_BODY), base)
assert_not_equal(scv_normalized_impl_hash(SRC_BODY), scv_normalized_impl_hash(SRC))
step "comment/formatting-only change: same interface id AND same impl hash"
assert_equal(scv_syntactic_interface_id("m", SRC_COMMENT), base)
assert_equal(scv_normalized_impl_hash(SRC_COMMENT), scv_normalized_impl_hash(SRC))
step "signature change: different interface id"
assert_not_equal(scv_syntactic_interface_id("m", SRC_SIG), base)
step "a field type change inside a struct changes the interface id (fields are part of the surface)"
val s1 = "struct P:\n    x: i64\n    y: i64\n\nenum C:\n    A\n    B\n"
val s2 = "struct P:\n    x: i64\n    y: text\n\nenum C:\n    A\n    B\n"
val s3 = "struct P:\n    x: i64\n    y: i64\n\nenum C:\n    A\n"
assert_not_equal(scv_syntactic_interface_id("m", s1), scv_syntactic_interface_id("m", s2))
assert_not_equal(scv_syntactic_interface_id("m", s1), scv_syntactic_interface_id("m", s3))
```

</details>

#### states its guarantee: no typed-HIR hash is claimed while the frontend has no extractor

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-HIR-FINGERPRINT-001
val rec = scv_hir_fingerprint("m", SRC)
step "the record carries version, syntactic interface id and normalized impl hash"
expect(rec).to_contain("fingerprint: scv/hir-fingerprint/v1")
expect(scv_fingerprint_field(rec, "syntactic_interface_id")).to_start_with("siface1:")
expect(scv_fingerprint_field(rec, "normalized_impl_hash")).to_start_with("nimpl1:")
step "the guarantee line says what the id proves — declared surface as text, not types"
expect(scv_fingerprint_field(rec, "guarantee")).to_contain("declared public surface")
expect(scv_fingerprint_field(rec, "guarantee")).to_contain("not type-checked")
step "typed_hir_hash is reported unavailable, never fabricated"
expect(scv_typed_hir_hash("m", SRC)).to_start_with("unavailable:")
expect(scv_fingerprint_field(rec, "typed_hir_hash")).to_start_with("unavailable:")
expect(rec.contains("semantic_hash")).to_equal(false)
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-HIR-FINGERPRINT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9959f31c3cf38be847ef26edce291a4514389f3bb9389e901f78a137ab5fd25d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9959f31c3cf38be847ef26edce291a4514389f3bb9389e901f78a137ab5fd25d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9959f31c3cf38be847ef26edce291a4514389f3bb9389e901f78a137ab5fd25d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/scv_hir_fingerprint_spec.spl
mirror: doc/06_spec/02_integration/app/scv_hir_fingerprint_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_hir_fingerprint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_hir_fingerprint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_hir_fingerprint_spec.spl:43:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reuses the compiler frontend's canonical compile-interface digest' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_hir_fingerprint_spec.spl:54:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'body-only and comment-only changes keep the interface id; a signature change does not' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_hir_fingerprint_spec.spl:72:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'states its guarantee: no typed-HIR hash is claimed while the frontend has no extractor' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
