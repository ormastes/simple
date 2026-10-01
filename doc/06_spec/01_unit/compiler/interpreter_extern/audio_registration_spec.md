# rt_audio_* Interpreter Registration (source-list-absent bucket)

> `rt_audio_*` (31 symbols, census bucket (a) "source-list-absent") is declared as `extern fn` throughout `src/lib` and `src/app`, and is implemented once, in C, at `src/runtime/runtime_audio.c` -- a real miniaudio-backed engine, not a capability stub. Before this fix the interpreter had no entry for the family at all, so every call died with the generic `unknown extern function: rt_audio_init`, indistinguishable from "no audio support".

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rt_audio_* Interpreter Registration (source-list-absent bucket)

`rt_audio_*` (31 symbols, census bucket (a) "source-list-absent") is declared as `extern fn` throughout `src/lib` and `src/app`, and is implemented once, in C, at `src/runtime/runtime_audio.c` -- a real miniaudio-backed engine, not a capability stub. Before this fix the interpreter had no entry for the family at all, so every call died with the generic `unknown extern function: rt_audio_init`, indistinguishable from "no audio support".

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter_extern/audio_registration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`rt_audio_*` (31 symbols, census bucket (a) "source-list-absent") is declared
as `extern fn` throughout `src/lib` and `src/app`, and is implemented once,
in C, at `src/runtime/runtime_audio.c` -- a real miniaudio-backed engine, not
a capability stub. Before this fix the interpreter had no entry for the
family at all, so every call died with the generic
`unknown extern function: rt_audio_init`, indistinguishable from "no audio
support".

Unlike the `rt_opengl_*`/`rt_oneapi_*` lane, `runtime_audio.c` was missing
from **both** C-source lists that gate linkage:

- the native-product-build list (`sources` array at
  `src/compiler/70.backend/backend/runtime_compiler.spl`), and
- the C sources `src/compiler_rust/runtime/build.rs` compiles into this
  crate's own staticlib/cdylib.

Both were fixed by adding `runtime_audio.c` to each list; no duplicate-symbol
risk exists (confirmed before landing: no other C or Rust source in this
crate defines any `rt_audio_*` name, so the whole file could be linked
directly, unlike `runtime_native.c`'s partial-extraction precedent).

`rt_audio_*` is not uniformly `int64_t`-in/`int64_t`-out like
`rt_opengl_*`/`rt_oneapi_*`: it mixes `int64_t` handles, `double`
(volume/position/distance), `const char*` (paths, the backend name), and one
`SplArray*`-taking entry point (`rt_audio_play_pcm_f32`), which is refused
cleanly rather than risking a bad transmute (same precedent as
`rt_sdl2_present_rgba`/`rt_glfw_present_argb`).

This spec proves the error TEXT changed (the resolution oracle -- exit status
alone is fail-open), not merely that the process exits non-zero.

## Related Specifications

- doc/08_tracking/bug/interpreter_extern_unreachable_names.md — bucket (a)
- doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md
- test/01_unit/compiler/interpreter_extern/opengl_registration_spec.spl — sibling lane, same probe pattern

## Scenarios

### rt_audio_* interpreter registration

#### rt_audio_backend_name: resolves through to the linked C implementation instead of failing to resolve

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rt_audio_backend_name: resolves through to the linked C implementation instead of failing to resolve
- Run the audio backend-name probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_audio_backend_name: resolves through to the linked C implementation instead of failing to resolve")
step("Run the audio backend-name probe fixture under the interpreter")
val (out, err, _code) = run_probe_child("test/fixture/interpreter_extern/audio_backend_name_probe.spl")
assert_true(out.contains("audio_backend_name_result="))
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_audio_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash

- rt_audio_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash
- Run the audio bogus-name probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_audio_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash")
step("Run the audio bogus-name probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/audio_bogus_probe.spl")
assert_true(err.contains("unknown rt_audio_"))
```

</details>

#### rt_audio_zzz_bogus: guard text is distinct from the generic unknown-extern text

- rt_audio_zzz_bogus: guard text is distinct from the generic unknown-extern text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_audio_zzz_bogus: guard text is distinct from the generic unknown-extern text")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/audio_bogus_probe.spl")
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_audio_play_pcm_f32: the one array-taking entry point is refused cleanly, not transmuted

- rt_audio_play_pcm_f32: the one array-taking entry point is refused cleanly, not transmuted
- Run the audio play_pcm_f32 probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_audio_play_pcm_f32: the one array-taking entry point is refused cleanly, not transmuted")
step("Run the audio play_pcm_f32 probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/audio_play_pcm_f32_probe.spl")
assert_true(err.contains("natively-linked"))
assert_equal(err.contains("unknown extern function"), false)
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
- `REQ-INTERP-EXTERN-AUDIO-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3138e45c09c44538d92011f5e03fc74dac2eb108d6ca5ac76e1a072637aa97d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3138e45c09c44538d92011f5e03fc74dac2eb108d6ca5ac76e1a072637aa97d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3138e45c09c44538d92011f5e03fc74dac2eb108d6ca5ac76e1a072637aa97d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interpreter_extern/audio_registration_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter_extern/audio_registration_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interpreter_extern/audio_registration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter_extern/audio_registration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter_extern/audio_registration_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/interpreter_extern/audio_registration_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_audio_backend_name: resolves through to the linked C implementation instead of failing to resolve' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter_extern/audio_registration_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_audio_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter_extern/audio_registration_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_audio_zzz_bogus: guard text is distinct from the generic unknown-extern text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
