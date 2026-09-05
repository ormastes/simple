# module_global_stale_shadow_class_spec

> Purpose: Prove that module-level state is read live regardless of payload type or writer depth.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# module_global_stale_shadow_class_spec

Purpose: Prove that module-level state is read live regardless of payload type or writer depth.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/module_global_stale_shadow_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that module-level state is read live regardless of payload type or writer depth.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### module-level state is read live regardless of payload type or writer depth

#### an i64 written by a free function is read live

- Write through a one-frame-deep helper
- The direct read must observe 7, not the -999 initialiser
   - Expected: g_int equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMP-MODULE-LEVEL-STATE-IS-READ-LIVE-REGARDLE-001
step("Write through a one-frame-deep helper")
set_int(7)

step("The direct read must observe 7, not the -999 initialiser")
expect(g_int).to_equal(7)
```

</details>

#### an i64 written TWO frames deep is read live

- an i64 written TWO frames deep is read live
- set_int_nested delegates to set_int, so the write happens two frames below this body
   - Expected: g_int equals `1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("an i64 written TWO frames deep is read live")
step("set_int_nested delegates to set_int, so the write happens two frames below this body")
set_int_nested(1234)
expect(g_int).to_equal(1234)
```

</details>

#### a text payload written by a helper is read live

- a text payload written by a helper is read live
- Verify: a text payload written by a helper is read live
   - Expected: g_text equals `live`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a text payload written by a helper is read live")
step("Verify: a text payload written by a helper is read live")
set_text("live")
expect(g_text).to_equal("live")
```

</details>

#### a bool payload written by a helper is read live

- a bool payload written by a helper is read live
- bool is the type most likely to read as a plausible-but-wrong value, since both states are legal
   - Expected: g_bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a bool payload written by a helper is read live")
step("bool is the type most likely to read as a plausible-but-wrong value, since both states are legal")
set_bool(true)
expect(g_bool).to_equal(true)
```

</details>

#### a container mutated in place by a helper is read live

- a container mutated in place by a helper is read live
- The array case differs from the scalar case: the handle may be shared while the contents are not
   - Expected: g_list.len() equals `2`
   - Expected: g_list[0] equals `5`
   - Expected: g_list[1] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a container mutated in place by a helper is read live")
step("The array case differs from the scalar case: the handle may be shared while the contents are not")
append_int(5)
append_int(6)
expect(g_list.len()).to_equal(2)
expect(g_list[0]).to_equal(5)
expect(g_list[1]).to_equal(6)
```

</details>

#### a write performed by a before_each hook is visible in the body

- a write performed by a before_each hook is visible in the body
- The hook runs in the same frame the body does; a stale copy taken before hooks ran would show 0
   - Expected: g_hook_witness equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a write performed by a before_each hook is visible in the body")
step("The hook runs in the same frame the body does; a stale copy taken before hooks ran would show 0")
expect(g_hook_witness).to_equal(42)
```

</details>

#### writes made in earlier examples are still visible in later ones

- writes made in earlier examples are still visible in later ones
- g_int was last set to 1234 by the two-frames-deep example; the container still holds both pushes
   - Expected: g_int equals `1234`
   - Expected: g_list.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("writes made in earlier examples are still visible in later ones")
step("g_int was last set to 1234 by the two-frames-deep example; the container still holds both pushes")
expect(g_int).to_equal(1234)
expect(g_list.len()).to_equal(2)
```

</details>

#### a write made directly in the body is visible to a later helper read

- a write made directly in the body is visible to a later helper read
- The reverse direction of the same two-store hazard: body writes env, helper reads the global store
   - Expected: g_int equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a write made directly in the body is visible to a later helper read")
step("The reverse direction of the same two-store hazard: body writes env, helper reads the global store")
g_int = 55
expect(g_int).to_equal(55)
```

</details>

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

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-MODULE-LEVEL-STATE-IS-READ-LIVE-REGARDLE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42efab25223699687cd2e5db89e7ed7ff78e75e296d3b2f88aab108b0381a0fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42efab25223699687cd2e5db89e7ed7ff78e75e296d3b2f88aab108b0381a0fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42efab25223699687cd2e5db89e7ed7ff78e75e296d3b2f88aab108b0381a0fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/module_global_stale_shadow_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/module_global_stale_shadow_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/module_global_stale_shadow_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/module_global_stale_shadow_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/module_global_stale_shadow_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/module_global_stale_shadow_class_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an i64 written by a free function is read live' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/module_global_stale_shadow_class_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an i64 written TWO frames deep is read live' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/module_global_stale_shadow_class_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a text payload written by a helper is read live' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
