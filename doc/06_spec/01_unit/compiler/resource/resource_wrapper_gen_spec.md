# Resource wrapper generation — WP-H acceptance

> WP-H builds on landed WP-D (convention inference). Emitter in:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resource wrapper generation — WP-H acceptance

WP-H builds on landed WP-D (convention inference). Emitter in:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Plan | doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-H) |
| Design | doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md §1 |
| Source | `test/01_unit/compiler/resource/resource_wrapper_gen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

WP-H builds on landed WP-D (convention inference). Emitter in:
`src/compiler/90.tools/sffi_gen/resource_wrapper_gen.spl`

Takes a FamilyClassificationResult and generates wrapper classes:
- Owning wrapper class with invalid sentinel check → Option-like return
- Methods that borrow self
- Consuming close() method with one-shot double-close guard
- Raw rt_* externs stay private

Golden-file spec: assert generated text shape for rt_file family.
Sabotage-verified: break sentinel check → fails, revert → passes.

## Scenarios

### resource wrapper generation: golden text output

#### generates wrapper class shape

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates wrapper class shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates wrapper class shape")
# Golden output for rt_file family
val golden = """extern fn rt_file_open(...) -> ...
```

</details>

#### generates consuming close with double-close guard

- generates consuming close with double-close guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates consuming close with double-close guard")
val golden = """    fn close():
# Consuming drop: one-shot guard against double-close
if self.handle != -1:
    rt_file_close(self.handle)
    self.handle = -1
```

</details>

#### sabotage: revert to valid version passes

- sabotage: revert to valid version passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sabotage: revert to valid version passes")
# This is the "revert it" test - confirms the check is necessary
val valid = """    static fn open(...) -> File?:
val h = rt_file_open(...)
if h == -1:
    nil
else:
    File(handle: h)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md (WP-H)`
- **Design:** `doc/05_design/language/resource/resource_sffi_binding_design_2026-08-06.md §1`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `96e9dc0f47f92065a769d2cbd790766e890b2f7b9f7f9f264081dfea0c3ac6d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96e9dc0f47f92065a769d2cbd790766e890b2f7b9f7f9f264081dfea0c3ac6d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96e9dc0f47f92065a769d2cbd790766e890b2f7b9f7f9f264081dfea0c3ac6d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/resource/resource_wrapper_gen_spec.spl
mirror: doc/06_spec/01_unit/compiler/resource/resource_wrapper_gen_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/resource/resource_wrapper_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/resource/resource_wrapper_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/resource/resource_wrapper_gen_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates wrapper class shape' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_wrapper_gen_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates acquire factory with sentinel check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/resource/resource_wrapper_gen_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates consuming close with double-close guard' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
