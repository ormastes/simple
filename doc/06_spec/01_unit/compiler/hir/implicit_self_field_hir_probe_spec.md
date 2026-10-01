# implicit_self_field_hir_probe_spec

> Probe: what does PURE-SIMPLE HIR lowering do with a bare `field = value`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# implicit_self_field_hir_probe_spec

Probe: what does PURE-SIMPLE HIR lowering do with a bare `field = value`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Probe: what does PURE-SIMPLE HIR lowering do with a bare `field = value`
assignment inside a `me` method, where `field` is a declared class field and
has no existing local binding? Executes the real `compiler.hir.hir_lowering`
module (not the Rust seed) via `parse_full_frontend` + `HirLowering.lower_module`.

## Scenarios

### pure-Simple HIR lowering: implicit self-field assignment

#### hard-errors on a bare field-name assignment (measured, not silent)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hard-errors on a bare field-name assignment (measured, not silent)
   - Expected: err_count equals `1`
   - Expected: lowering.lowering_error_is_recovered_at(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("hard-errors on a bare field-name assignment (measured, not silent)")
val log = make_logger()
val module = parse_full_frontend(IMPLICIT_SRC, "implicit", "implicit", log)
var lowering = HirLowering.with_filename("implicit")
lowering.lower_module(module)
val err_count = lowering.lowering_error_count()
print("PROBE[implicit]_ERROR_COUNT=" + err_count.to_text())
print("PROBE[implicit]_DIAG[0]=" + lowering.diagnostic_messages[0])
expect(err_count).to_equal(1)
# Distinguish a HARD error (compilation refuses to proceed) from a
# `recovered()` diagnostic (noted, but the pipeline carries on with
# HirExprKind.Error in the tree). lower_unresolved_ident calls
# self.error(...), not self.recovered(...) -- confirm that here rather
# than inferring it from the source read alone.
expect(lowering.lowering_error_is_recovered_at(0)).to_equal(false)
```

</details>

#### still accepts the explicit self.field form with zero diagnostics

- still accepts the explicit self.field form with zero diagnostics
   - Expected: err_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still accepts the explicit self.field form with zero diagnostics")
val err_count = diag_count(EXPLICIT_SRC, "explicit")
expect(err_count).to_equal(0)
```

</details>

#### has NO implicit-local-declaration path at all -- errors on bare non-field assignment too (seed/pure-Simple divergence, filed separately, not fixed here)

- has NO implicit-local-declaration path at all -- errors on bare non-field assignment too (seed/pure-Simple divergence, filed separately, not fixed here)
   - Expected: err_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has NO implicit-local-declaration path at all -- errors on bare non-field assignment too (seed/pure-Simple divergence, filed separately, not fixed here)")
val err_count = diag_count(PLAIN_LOCAL_SRC, "plain_local")
expect(err_count).to_equal(2)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fc8bbcccfefe9d9654c3129136cf0164884e3040f1343e213b822fab9cdb688a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc8bbcccfefe9d9654c3129136cf0164884e3040f1343e213b822fab9cdb688a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc8bbcccfefe9d9654c3129136cf0164884e3040f1343e213b822fab9cdb688a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hard-errors on a bare field-name assignment (measured, not silent)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still accepts the explicit self.field form with zero diagnostics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/implicit_self_field_hir_probe_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has NO implicit-local-declaration path at all -- errors on bare non-field assignment too (seed/pure-Simple divergence, filed separately, not fixed here)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
