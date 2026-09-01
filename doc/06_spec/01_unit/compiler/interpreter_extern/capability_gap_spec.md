# M3 Honest Capability-Gap Arms (rt_webgpu_ / rt_vk_ / rt_gui_ / rt_lyon_ / rt_gamepad_)

> `rt_webgpu_*`, `rt_vk_*`, `rt_gui_*`, `rt_lyon_*`, and `rt_gamepad_*` are declared as `extern fn` throughout `src/lib` and `src/app`, but unlike `rt_sdl2_*`/`rt_glfw_*`/`rt_vulkan_*` there is no real native implementation anywhere in this tree to register them against (no C translation unit, no linked Rust runtime crate). `rt_lyon_*` alone has 49 call sites and `rt_gamepad_*` 20, with zero native definitions between them.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# M3 Honest Capability-Gap Arms (rt_webgpu_ / rt_vk_ / rt_gui_ / rt_lyon_ / rt_gamepad_)

`rt_webgpu_*`, `rt_vk_*`, `rt_gui_*`, `rt_lyon_*`, and `rt_gamepad_*` are declared as `extern fn` throughout `src/lib` and `src/app`, but unlike `rt_sdl2_*`/`rt_glfw_*`/`rt_vulkan_*` there is no real native implementation anywhere in this tree to register them against (no C translation unit, no linked Rust runtime crate). `rt_lyon_*` alone has 49 call sites and `rt_gamepad_*` 20, with zero native definitions between them.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter_extern/capability_gap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`rt_webgpu_*`, `rt_vk_*`, `rt_gui_*`, `rt_lyon_*`, and `rt_gamepad_*` are
declared as `extern fn` throughout `src/lib` and `src/app`, but unlike
`rt_sdl2_*`/`rt_glfw_*`/`rt_vulkan_*` there is no real native implementation
anywhere in this tree to register them against (no C translation unit, no
linked Rust runtime crate). `rt_lyon_*` alone has 49 call sites and
`rt_gamepad_*` 20, with zero native definitions between them.

Before this lane, every call into one of these five families under the
interpreter died with the generic `unknown extern function: rt_lyon_...`
error — indistinguishable from a typo or a symbol that was never declared
anywhere. `capability_gap.rs` intercepts the five prefixes first (see
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`, the arm right
before the generic `dynamic_sffi` fallback) and returns a structured,
family-named capability-gap error instead, so a caller can tell "not built on
this host" apart from "does not exist anywhere yet".

This spec proves the error TEXT changed (the resolution oracle — exit status
alone is fail-open), not merely that the process exits non-zero.

## Related Specifications

- doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md — lane R3
- doc/04_architecture/runtime/native_library_binding_survey.md §1

## Scenarios

### M3 capability-gap arms: rt_webgpu_ / rt_vk_ / rt_gui_ / rt_lyon_ / rt_gamepad_

#### rt_webgpu_adapter_count: error names the family as a capability gap

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rt_webgpu_adapter_count: error names the family as a capability gap
- Run the webgpu probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_webgpu_adapter_count: error names the family as a capability gap")
step("Run the webgpu probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/webgpu_capability_gap_probe.spl")
assert_true(err.contains("rt_webgpu"))
assert_true(err.contains("capability gap"))
```

</details>

#### rt_webgpu_adapter_count: error text is no longer the generic unknown-extern text

- rt_webgpu_adapter_count: error text is no longer the generic unknown-extern text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_webgpu_adapter_count: error text is no longer the generic unknown-extern text")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/webgpu_capability_gap_probe.spl")
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_vk_cleanup: error names the family as a capability gap (not rt_vulkan_)

- rt_vk_cleanup: error names the family as a capability gap (not rt_vulkan_)
- Run the rt_vk_ probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_vk_cleanup: error names the family as a capability gap (not rt_vulkan_)")
step("Run the rt_vk_ probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/vk_capability_gap_probe.spl")
assert_true(err.contains("rt_vk"))
assert_true(err.contains("capability gap"))
```

</details>

#### rt_vk_cleanup: error text is no longer the generic unknown-extern text

- rt_vk_cleanup: error text is no longer the generic unknown-extern text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_vk_cleanup: error text is no longer the generic unknown-extern text")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/vk_capability_gap_probe.spl")
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_gui_present_html: error names the family as a capability gap

- rt_gui_present_html: error names the family as a capability gap
- Run the gui probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_gui_present_html: error names the family as a capability gap")
step("Run the gui probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/gui_capability_gap_probe.spl")
assert_true(err.contains("rt_gui"))
assert_true(err.contains("capability gap"))
```

</details>

#### rt_gui_present_html: error text is no longer the generic unknown-extern text

- rt_gui_present_html: error text is no longer the generic unknown-extern text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_gui_present_html: error text is no longer the generic unknown-extern text")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/gui_capability_gap_probe.spl")
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_lyon_fill_tessellation_free: error names the family as a capability gap

- rt_lyon_fill_tessellation_free: error names the family as a capability gap
- Run the lyon probe fixture under the interpreter (largest family: 49 call sites)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_lyon_fill_tessellation_free: error names the family as a capability gap")
step("Run the lyon probe fixture under the interpreter (largest family: 49 call sites)")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/lyon_capability_gap_probe.spl")
assert_true(err.contains("rt_lyon"))
assert_true(err.contains("capability gap"))
```

</details>

#### rt_lyon_fill_tessellation_free: error text is no longer the generic unknown-extern text

- rt_lyon_fill_tessellation_free: error text is no longer the generic unknown-extern text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_lyon_fill_tessellation_free: error text is no longer the generic unknown-extern text")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/lyon_capability_gap_probe.spl")
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_gamepad_count: error names the family as a capability gap

- rt_gamepad_count: error names the family as a capability gap
- Run the gamepad probe fixture under the interpreter (20 call sites)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_gamepad_count: error names the family as a capability gap")
step("Run the gamepad probe fixture under the interpreter (20 call sites)")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/gamepad_capability_gap_probe.spl")
assert_true(err.contains("rt_gamepad"))
assert_true(err.contains("capability gap"))
```

</details>

#### rt_gamepad_count: error text is no longer the generic unknown-extern text

- rt_gamepad_count: error text is no longer the generic unknown-extern text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_gamepad_count: error text is no longer the generic unknown-extern text")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/gamepad_capability_gap_probe.spl")
assert_equal(err.contains("unknown extern function"), false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-INTERP-EXTERN-CAPGAP-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `359d096f47f5acaeb6c1269bc7a5c451972750190be94600487ebf3a962b9997`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `359d096f47f5acaeb6c1269bc7a5c451972750190be94600487ebf3a962b9997`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `359d096f47f5acaeb6c1269bc7a5c451972750190be94600487ebf3a962b9997`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interpreter_extern/capability_gap_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter_extern/capability_gap_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interpreter_extern/capability_gap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter_extern/capability_gap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter_extern/capability_gap_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/interpreter_extern/capability_gap_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_webgpu_adapter_count: error names the family as a capability gap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter_extern/capability_gap_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_webgpu_adapter_count: error text is no longer the generic unknown-extern text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter_extern/capability_gap_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_vk_cleanup: error names the family as a capability gap (not rt_vulkan_)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
