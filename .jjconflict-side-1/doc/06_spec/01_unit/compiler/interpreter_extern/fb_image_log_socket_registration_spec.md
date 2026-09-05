# rt_fb_*/rt_image_*/rt_simpleos_log_*+rt_log_target_*/rt_socket_set_nonblocking

> After the `rt_audio_*` lane fixed 31 of bucket (a)'s 51 "source-list-absent" names (doc/08_tracking/bug/interpreter_extern_unreachable_names.md), 20 remained, spanning 4 unrelated files/subsystems:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rt_fb_*/rt_image_*/rt_simpleos_log_*+rt_log_target_*/rt_socket_set_nonblocking

After the `rt_audio_*` lane fixed 31 of bucket (a)'s 51 "source-list-absent" names (doc/08_tracking/bug/interpreter_extern_unreachable_names.md), 20 remained, spanning 4 unrelated files/subsystems:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

After the `rt_audio_*` lane fixed 31 of bucket (a)'s 51
"source-list-absent" names (doc/08_tracking/bug/interpreter_extern_unreachable_names.md),
20 remained, spanning 4 unrelated files/subsystems:

- `runtime_framebuffer.c` (`rt_fb_fill32`, `rt_fb_blit32` -- 2 names): already
  compiled into the interpreter crate's own C sources
  (`src/compiler_rust/runtime/build.rs`), but nothing declared or called the
  symbols from Rust, so no interpreter dispatch entry existed. Only the
  native-product-build source list
  (`src/compiler/70.backend/backend/runtime_compiler.spl`) and the dispatch
  entry needed fixing.
- `runtime_image.c` (`rt_image_*` -- 6 names, `stb_image`-backed): absent
  from both C-source lists, same shape as `rt_audio_*`.
- Baremetal `runtime_minimal.c`/`runtime_log.c`: `rt_mmio_*` (6 names) is
  genuinely baremetal-only -- every call site is SimpleOS
  kernel/baremetal-tier code (`nogc_async_mut_noalloc/baremetal/*.spl`,
  `os/gui/render.spl`, `os/drivers/virtio/*`), never reachable from a hosted
  interpreter session, so it is correctly left unregistered. `rt_simpleos_log_*`
  + `rt_log_target_*` (5 names) is different: a deliberate *hosted* fallback
  implementation already exists at
  `src/runtime/startup/common/runtime_log_hosted.c` (returns `false`
  unconditionally -- the log lib falls through to `println` on `false`,
  which is correct hosted behavior, not a stub for missing work), separate
  from the real baremetal implementation in
  `src/runtime/startup/baremetal/runtime_log.c` (never compiled here). Only
  the hosted file was absent from the interpreter crate's C sources.
- `platform/async_linux_epoll.c` (`rt_socket_set_nonblocking` -- 1 name):
  the whole file is gated `#if defined(__linux__)` and pulls in
  `spl_array_new_i64`/`spl_array_push_i64` (defined in `runtime.c`, not
  compiled by this crate) via a sibling function, `rt_epoll_wait` --
  the same problem `rt_audio_play_pcm_f32` had. Its only caller
  (`src/lib/nogc_sync_mut/fs/nvfs_posix/posix_driver.spl`) is hosted POSIX
  code, not baremetal, so this is a real gap. The single, dependency-free
  function body was extracted verbatim into
  `src/runtime/runtime_socket_nonblock.c` (portable to any non-Windows
  target, matching the `runtime_native_gpu_stub.c` partial-extraction
  precedent), rather than linking the whole epoll-backed file.

This spec proves the error TEXT changed (the resolution oracle -- exit
status alone is fail-open), not merely that the process exits non-zero,
matching the `rt_audio_*` lane's proof shape.

## Related Specifications

- doc/08_tracking/bug/interpreter_extern_unreachable_names.md — bucket (a)
- doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md
- test/01_unit/compiler/interpreter_extern/audio_registration_spec.spl — sibling lane, same probe pattern

## Scenarios

### rt_fb_* interpreter registration

#### rt_fb_fill32: resolves through to the linked C implementation instead of failing to resolve

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rt_fb_fill32: resolves through to the linked C implementation instead of failing to resolve
- Run the fb fill32 probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_fb_fill32: resolves through to the linked C implementation instead of failing to resolve")
step("Run the fb fill32 probe fixture under the interpreter")
val (out, err, _code) = run_probe_child("test/fixture/interpreter_extern/fb_fill32_probe.spl", "fb_fill32_result=")
assert_true(out.contains("fb_fill32_result=ok"))
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_fb_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash

- rt_fb_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash
- Run the fb bogus-name probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_fb_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash")
step("Run the fb bogus-name probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/fb_bogus_probe.spl", "fb_fill32_result=")
assert_true(err.contains("unknown rt_fb_*"))
assert_equal(err.contains("unknown extern function"), false)
```

</details>

### rt_image_* interpreter registration

#### rt_image_load: resolves through to the linked C implementation instead of failing to resolve

- rt_image_load: resolves through to the linked C implementation instead of failing to resolve
- Run the image load probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_image_load: resolves through to the linked C implementation instead of failing to resolve")
step("Run the image load probe fixture under the interpreter")
val (out, err, _code) = run_probe_child("test/fixture/interpreter_extern/image_load_probe.spl", "image_load_result=")
assert_true(out.contains("image_load_result=0"))
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_image_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash

- rt_image_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash
- Run the image bogus-name probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_image_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash")
step("Run the image bogus-name probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/image_bogus_probe.spl", "image_load_result=")
assert_true(err.contains("unknown rt_image_*"))
assert_equal(err.contains("unknown extern function"), false)
```

</details>

### rt_simpleos_log_*/rt_log_target_* interpreter registration

#### rt_simpleos_log_init: resolves through to the hosted fallback implementation instead of failing to resolve

- rt_simpleos_log_init: resolves through to the hosted fallback implementation instead of failing to resolve
- Run the simpleos_log init probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_simpleos_log_init: resolves through to the hosted fallback implementation instead of failing to resolve")
step("Run the simpleos_log init probe fixture under the interpreter")
val (out, err, _code) = run_probe_child("test/fixture/interpreter_extern/simpleos_log_init_probe.spl", "simpleos_log_init_result=")
assert_true(out.contains("simpleos_log_init_result=false"))
assert_equal(err.contains("unknown extern function"), false)
```

</details>

#### rt_simpleos_log_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash

- rt_simpleos_log_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash
- Run the simpleos_log bogus-name probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rt_simpleos_log_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash")
step("Run the simpleos_log bogus-name probe fixture under the interpreter")
val (_out, err, _code) = run_probe_child("test/fixture/interpreter_extern/simpleos_log_bogus_probe.spl", "simpleos_log_init_result=")
assert_true(err.contains("unknown hosted log-lib"))
assert_equal(err.contains("unknown extern function"), false)
```

</details>

### rt_socket_set_nonblocking interpreter registration

#### resolves through to the linked C implementation instead of failing to resolve

- resolves through to the linked C implementation instead of failing to resolve
- Run the socket nonblock probe fixture under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves through to the linked C implementation instead of failing to resolve")
step("Run the socket nonblock probe fixture under the interpreter")
val (out, err, _code) = run_probe_child("test/fixture/interpreter_extern/socket_nonblock_probe.spl", "socket_nonblock_result=")
assert_true(out.contains("socket_nonblock_result=false"))
assert_equal(err.contains("unknown extern function"), false)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-INTERP-EXTERN-BUCKET-A-REMAINDER-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `943b175925c4fbcc10f117419ac1021c5da27d15a462a60fb80712ab35224e12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `943b175925c4fbcc10f117419ac1021c5da27d15a462a60fb80712ab35224e12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `943b175925c4fbcc10f117419ac1021c5da27d15a462a60fb80712ab35224e12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_fb_fill32: resolves through to the linked C implementation instead of failing to resolve' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_fb_zzz_bogus: a prefix name with no C definition gets the family guard, not a crash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter_extern/fb_image_log_socket_registration_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_image_load: resolves through to the linked C implementation instead of failing to resolve' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
