# rt_oneapi_* Interpreter Registration (Lane R2)

> `rt_oneapi_*` (14 symbols) is declared as `extern fn` throughout `src/lib` and `src/app`, and is implemented once, in C, at `src/runtime/runtime_native.c` -- as a fixed-value capability stub (no real oneAPI/SYCL binding; every entry point returns `false`/`0`/`-3`). Before this lane the interpreter had no entry for the family at all, so every call died with the generic `unknown extern function: rt_oneapi_init`, indistinguishable from "no oneAPI available".

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rt_oneapi_* Interpreter Registration (Lane R2)

`rt_oneapi_*` (14 symbols) is declared as `extern fn` throughout `src/lib` and `src/app`, and is implemented once, in C, at `src/runtime/runtime_native.c` -- as a fixed-value capability stub (no real oneAPI/SYCL binding; every entry point returns `false`/`0`/`-3`). Before this lane the interpreter had no entry for the family at all, so every call died with the generic `unknown extern function: rt_oneapi_init`, indistinguishable from "no oneAPI available".

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter_extern/oneapi_registration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`rt_oneapi_*` (14 symbols) is declared as `extern fn` throughout `src/lib`
and `src/app`, and is implemented once, in C, at
`src/runtime/runtime_native.c` -- as a fixed-value capability stub (no real
oneAPI/SYCL binding; every entry point returns `false`/`0`/`-3`). Before this
lane the interpreter had no entry for the family at all, so every call died
with the generic `unknown extern function: rt_oneapi_init`, indistinguishable
from "no oneAPI available".

Same investigation as the sibling `rt_opengl_*` spec: the M2 hypothesis (same
shape as the rt_sdl2_* lane) checked out one list further in than the plan's
named location. `runtime_native.c` (which defines both `rt_opengl_*` and
`rt_oneapi_*`) was already present in the native-product-build source list
(`runtime_compiler.spl:268`), but absent from the C sources
`src/compiler_rust/runtime/build.rs` compiles into this crate's own
staticlib/cdylib -- the list that actually gates interpreter/seed linkage. R2
added `runtime_native.c` there and this module supplies the typed
registration on top (`oneapi.rs`, `unsafe extern "C"` linked directly -- no
dlopen needed, since the family has no header/link dependency to gate).

This spec proves the error TEXT changed (the resolution oracle -- exit status
alone is fail-open), not merely that the process exits non-zero.

## Related Specifications

- doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md — lane R2
- doc/04_architecture/runtime/native_library_binding_survey.md §1

## Scenarios

### rt_oneapi_* interpreter registration

#### rt_oneapi_init: resolves through to the linked C stub instead of failing to resolve

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rt_oneapi_init: resolves through to the linked C stub instead of failing to resolve
- Run the oneapi init probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_oneapi_init: resolves through to the linked C stub instead of failing to resolve")
step("Run the oneapi init probe fixture under the interpreter")
val (out, err, _code) = run_probe_child("test/fixture/interpreter_extern/oneapi_init_probe.spl")
assert_true(out.contains("oneapi_init_result=false"))
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_oneapi_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash

- rt_oneapi_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash
- Run the oneapi bogus-name probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_oneapi_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash")
step("Run the oneapi bogus-name probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/oneapi_bogus_probe.spl")
assert_true(err.contains("unknown rt_oneapi_"))
```

</details>

#### rt_oneapi_zzz_bogus: guard text is distinct from the generic unknown-extern text

- rt_oneapi_zzz_bogus: guard text is distinct from the generic unknown-extern text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_oneapi_zzz_bogus: guard text is distinct from the generic unknown-extern text")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/oneapi_bogus_probe.spl")
assert_equal(err.contains("unknown extern function"), false)
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

- `REQ-SSPEC-UNIT`
- `REQ-INTERP-EXTERN-ONEAPI-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `88cd842287c2c8e9f7249a0524518d3a131b60641892ff3eee6a6fc4fc21a38a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88cd842287c2c8e9f7249a0524518d3a131b60641892ff3eee6a6fc4fc21a38a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88cd842287c2c8e9f7249a0524518d3a131b60641892ff3eee6a6fc4fc21a38a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interpreter_extern/oneapi_registration_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter_extern/oneapi_registration_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interpreter_extern/oneapi_registration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter_extern/oneapi_registration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter_extern/oneapi_registration_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/interpreter_extern/oneapi_registration_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_oneapi_init: resolves through to the linked C stub instead of failing to resolve' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter_extern/oneapi_registration_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_oneapi_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter_extern/oneapi_registration_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_oneapi_zzz_bogus: guard text is distinct from the generic unknown-extern text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
