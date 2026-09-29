# rt_glfw_* Interpreter Registration (Lane R1)

> `rt_glfw_* ` (41 exported C functions, generated from `src/runtime/runtime_glfw.c`) is declared as `extern fn` throughout `src/lib` and `src/app`, and is implemented once, in C, at `src/runtime/runtime_glfw.c`. Native builds link that translation unit directly (it is in the default runtime source list, `runtime_compiler.spl:268`). The interpreter runs inside a separate process image (the Rust seed) that does not compile `runtime_glfw.c` into itself, so before this lane every call died with the generic `unknown extern function: rt_glfw_init`, indistinguishable from "no GLFW available".

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rt_glfw_* Interpreter Registration (Lane R1)

`rt_glfw_* ` (41 exported C functions, generated from `src/runtime/runtime_glfw.c`) is declared as `extern fn` throughout `src/lib` and `src/app`, and is implemented once, in C, at `src/runtime/runtime_glfw.c`. Native builds link that translation unit directly (it is in the default runtime source list, `runtime_compiler.spl:268`). The interpreter runs inside a separate process image (the Rust seed) that does not compile `runtime_glfw.c` into itself, so before this lane every call died with the generic `unknown extern function: rt_glfw_init`, indistinguishable from "no GLFW available".

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter_extern/glfw_registration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`rt_glfw_* ` (41 exported C functions, generated from
`src/runtime/runtime_glfw.c`) is declared as `extern fn` throughout `src/lib`
and `src/app`, and is implemented once, in C, at `src/runtime/runtime_glfw.c`.
Native builds link that translation unit directly (it is in the default
runtime source list, `runtime_compiler.spl:268`). The interpreter runs
inside a separate process image (the Rust seed) that does not compile
`runtime_glfw.c` into itself, so before this lane every call died with the
generic `unknown extern function: rt_glfw_init`, indistinguishable from "no
GLFW available".

This is the M1 shape (registration gap, not a source-list gap): the fix adds
a typed dispatch table (`interpreter_extern/glfw.rs`, mirroring the
`rt_sdl2_*` satellite-dlopen precedent) resolving the same C symbols out of
a `libspl_glfw.{so,dylib,dll}` satellite. On this host `libglfw.so.3` is not
installed and no satellite has been built, so a resolved call still errors --
but with a GLFW-specific message, never the generic "unknown extern
function" text. That text change is the resolution oracle this spec proves
(exit status alone is fail-open).

## Related Specifications

- doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md — lane R1
- doc/04_architecture/runtime/native_library_binding_survey.md §1

## Scenarios

### rt_glfw_* interpreter registration

#### rt_glfw_init: resolves through to the GLFW family dispatch instead of failing to resolve

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rt_glfw_init: resolves through to the GLFW family dispatch instead of failing to resolve
- Run the glfw init probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_glfw_init: resolves through to the GLFW family dispatch instead of failing to resolve")
step("Run the glfw init probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/glfw_init_probe.spl")
assert_true(err.contains("GLFW runtime library"))
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_glfw_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash

- rt_glfw_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash
- Run the glfw bogus-name probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_glfw_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash")
step("Run the glfw bogus-name probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/glfw_bogus_probe.spl")
assert_true(err.contains("unknown GLFW extern function"))
```

</details>

#### rt_glfw_zzz_bogus: guard text is distinct from the generic unknown-extern text

- rt_glfw_zzz_bogus: guard text is distinct from the generic unknown-extern text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_glfw_zzz_bogus: guard text is distinct from the generic unknown-extern text")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/glfw_bogus_probe.spl")
assert_equal(err.contains("unknown extern function:"), false)
```

</details>

#### rt_glfw_present_argb: the array-taking entry point is refused with an explanation, not a crash

- rt_glfw_present_argb: the array-taking entry point is refused with an explanation, not a crash
- Run the glfw present_argb probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_glfw_present_argb: the array-taking entry point is refused with an explanation, not a crash")
step("Run the glfw present_argb probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/glfw_present_argb_probe.spl")
assert_true(err.contains("natively-linked"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-INTERP-EXTERN-GLFW-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `31d5cd231c7b3fd82a7931f3e829b6e928ad5803552dd5edfccb922531b8db6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `31d5cd231c7b3fd82a7931f3e829b6e928ad5803552dd5edfccb922531b8db6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `31d5cd231c7b3fd82a7931f3e829b6e928ad5803552dd5edfccb922531b8db6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interpreter_extern/glfw_registration_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter_extern/glfw_registration_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interpreter_extern/glfw_registration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter_extern/glfw_registration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter_extern/glfw_registration_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/interpreter_extern/glfw_registration_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_glfw_init: resolves through to the GLFW family dispatch instead of failing to resolve' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter_extern/glfw_registration_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_glfw_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter_extern/glfw_registration_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_glfw_zzz_bogus: guard text is distinct from the generic unknown-extern text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
