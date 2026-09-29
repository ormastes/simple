# WM/GUI Host Seam — False-Success Stub Guard

> A platform seam implementation that FALSELY REPORTS SUCCESS is worse than one

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM/GUI Host Seam — False-Success Stub Guard

A platform seam implementation that FALSELY REPORTS SUCCESS is worse than one

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/gui/wm_host_platform/wm_host_false_success_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A platform seam implementation that FALSELY REPORTS SUCCESS is worse than one
that is missing: a missing implementation is visible, a lying one is not.
This file fails on that shape.

## Scope and Preconditions

Three stub shapes are covered, each with a general rule rather than a
match on one known site:

1. **Unfalsifiable self-report.** A backend that advertises "I am using
   native platform symbols" must not do so unconditionally. If the claim is
   a hardcoded constant it stays `true` on hosts where those symbols provably
   do not exist, so it can never be wrong and therefore never means anything.

2. **Constant provenance.** A backend with a real device-present path must be
   CAPABLE of reporting a device-sourced readback. If its readback provenance
   is a hardcoded literal, a device-backed present is indistinguishable from
   a CPU fallback. This is the shape at
   `src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl`, whose
   `read_pixels_with_source` returns `engine2d_readback(self.buf,
   "cpu_mirror")` unconditionally while `present()` really does branch on
   `self.gpu_ready and self.surface != 0`. Contrast
   `backend_virtio_gpu.spl`, which selects `device_readback` vs `cpu_mirror`
   from actual device state. A backend with NO device path (e.g.
   `backend_metal.spl`) is honestly CPU-only and is exempt.

3. **Unreachable dispatch.** A platform-aware selector that nothing calls
   does not make the seam portable; it only makes the codebase LOOK
   portable. `select_hosted_backend` in `src/os/compositor/hosted_backend.spl`
   is such a selector.

## Recovery and Troubleshooting

A RED result here is a real defect in the platform seam, not a flaky test.
Each example names the file and the shape.

## Compatibility and Limitations

Rules 1 and 3 are evaluated against the EXECUTING host, so they get stronger,
not weaker, as the suite runs on more platforms. Rule 2 is a source-shape
check and is host-independent.

## Scenarios

### WM host seam — native-symbol self-reports must be falsifiable

#### macos backend does not claim native cocoa symbols on a non-macos host

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- macos backend does not claim native cocoa symbols on a non-macos host
   - Expected: HostedCocoaBackend.uses_native_cocoa_symbols() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("macos backend does not claim native cocoa symbols on a non-macos host")
# EXPECTED RED on Linux. `uses_native_cocoa_symbols()` is a hardcoded
# `true` (hosted_backend_cocoa.spl), so it claims native Cocoa on a
# host where `rt_cocoa_window_new` does not even exist as an extern —
# constructing the backend here fails with `unknown extern function`.
# A claim that cannot be false is not evidence of anything.
if host_os() != "macos":
    expect(HostedCocoaBackend.uses_native_cocoa_symbols()).to_equal(false)
```

</details>

#### windows backend does not claim native win32 symbols on a non-windows host

- windows backend does not claim native win32 symbols on a non-windows host
   - Expected: HostedWin32Backend.uses_native_win32_symbols() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("windows backend does not claim native win32 symbols on a non-windows host")
# EXPECTED RED on Linux, same shape (hosted_backend_win32.spl).
if host_os() != "windows":
    expect(HostedWin32Backend.uses_native_win32_symbols()).to_equal(false)
```

</details>

#### a backend claiming native symbols is gated by a real build feature

- a backend claiming native symbols is gated by a real build feature
   - Expected: file_exists("src/runtime/hosted/Cargo.toml") is true
   - Expected: HostedCocoaBackend.uses_native_cocoa_symbols() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a backend claiming native symbols is gated by a real build feature")
# The real Cocoa/Win32 code is behind `cocoa-real` / `win32-real` in
# src/runtime/hosted/Cargo.toml, whose `default = []`. So the DEFAULT
# build compiles the sentinel branch that returns -1/false, while the
# Simple-side self-report still says the native path is in use.
expect(file_exists("src/runtime/hosted/Cargo.toml")).to_equal(true)
val gated = source_contains("src/runtime/hosted/Cargo.toml", "default = []")
# If the features are off by default, no Simple-side backend may
# report native symbol use unconditionally.
if gated and host_os() != "macos":
    expect(HostedCocoaBackend.uses_native_cocoa_symbols()).to_equal(false)
```

</details>

### WM host seam — readback provenance must reflect device state

#### webgpu backend has a device-present path

- webgpu backend has a device-present path
   - Expected: has_device_present_path("webgpu") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("webgpu backend has a device-present path")
# Establishes the premise of the next example, so that a RED there
# cannot be dismissed as "it is just a CPU backend".
expect(has_device_present_path("webgpu")).to_equal(true)
```

</details>

#### webgpu backend can report a device-sourced readback

- webgpu backend can report a device-sourced readback
   - Expected: can_report_device_readback("webgpu") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("webgpu backend can report a device-sourced readback")
# EXPECTED RED. `read_pixels_with_source` returns the literal
# "cpu_mirror" unconditionally, so a real GPU present is
# indistinguishable from a CPU fallback.
expect(can_report_device_readback("webgpu")).to_equal(true)
```

</details>

#### virtio-gpu backend proves the correct shape is achievable

- virtio-gpu backend proves the correct shape is achievable
   - Expected: can_report_device_readback("virtio_gpu") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("virtio-gpu backend proves the correct shape is achievable")
# Positive control. Without this, a RED above could be a broken
# detector rather than a real defect.
expect(can_report_device_readback("virtio_gpu")).to_equal(true)
```

</details>

#### every gpu backend with a device path can report device provenance

- every gpu backend with a device path can report device provenance
   - Expected: can_report_device_readback(n) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("every gpu backend with a device path can report device provenance")
# The general rule. Backends with no device path are exempt.
var i = 0
val names = ["webgpu", "virtio_gpu", "cuda", "directx", "vulkan", "metal"]
while i < names.len():
    val n = names[i]
    if file_exists(gpu_backend_path(n)) and has_device_present_path(n):
        expect(can_report_device_readback(n)).to_equal(true)
    i = i + 1
```

</details>

### WM host seam — platform dispatch must be reachable

#### a platform-aware backend selector exists

- a platform-aware backend selector exists
   - Expected: source_contains("src/os/compositor/hosted_backend.spl", "fn select_hosted_backend") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("a platform-aware backend selector exists")
expect(source_contains("src/os/compositor/hosted_backend.spl", "fn select_hosted_backend")).to_equal(true)
```

</details>

#### the platform-aware selector has at least one caller outside its own file

- the platform-aware selector has at least one caller outside its own file
   - Expected: callers != "" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the platform-aware selector has at least one caller outside its own file")
# This guard was RED when written: `select_hosted_backend` was
# referenced only by its own definition and two comments in the same
# file, so every live path fell through to
# HeadlessHostCompositorBackend and the macOS and Windows backends
# were unreachable in production. It went GREEN when
# `host_compositor_bootstrap.spl` was wired to call the selector.
# Keep it: it is what stops the dispatch from silently regressing to
# unreachable again.
val cmd = "grep -rl --include=*.spl 'select_hosted_backend' src/ 2>/dev/null | grep -v 'compositor/hosted_backend.spl' | head -1"
val callers = shell_output(cmd).trim()
expect(callers != "").to_equal(true)
```

</details>

#### the selector's platform arms call constructors that exist

- the selector's platform arms call constructors that exist
   - Expected: source_contains(sel, "HostedCocoaBackend") is true
   - Expected: source_contains(sel, "HostedWin32Backend") is true
   - Expected: source_contains(cocoa, "static fn create(") is true
   - Expected: source_contains(cocoa, "static fn try_create(") is true
   - Expected: source_contains(win32, "static fn create(") is true
   - Expected: source_contains(win32, "static fn try_create(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the selector's platform arms call constructors that exist")
# Historically the cocoa/win32 arms called a four-argument
# `.create(w, h, title, fill)` that those classes never defined, so
# the arms could not have resolved even if something had called the
# selector.
#
# NON-VACUITY: the two unconditional expectations below are what stop
# this example from silently asserting nothing if the arms are
# renamed or removed. An earlier revision of this guard consisted
# only of the conditional and passed vacuously the moment the
# constructor name changed.
val sel = "src/os/compositor/hosted_backend.spl"
val cocoa = "src/os/compositor/hosted_backend_cocoa.spl"
val win32 = "src/os/compositor/hosted_backend_win32.spl"
expect(source_contains(sel, "HostedCocoaBackend")).to_equal(true)
expect(source_contains(sel, "HostedWin32Backend")).to_equal(true)
# Whichever constructor form each arm invokes must be defined.
if source_contains(sel, "HostedCocoaBackend.create("):
    expect(source_contains(cocoa, "static fn create(")).to_equal(true)
if source_contains(sel, "HostedCocoaBackend.try_create("):
    expect(source_contains(cocoa, "static fn try_create(")).to_equal(true)
if source_contains(sel, "HostedWin32Backend.create("):
    expect(source_contains(win32, "static fn create(")).to_equal(true)
if source_contains(sel, "HostedWin32Backend.try_create("):
    expect(source_contains(win32, "static fn try_create(")).to_equal(true)
```

</details>

### WM host seam — absent platforms must report unimplemented

#### freebsd is not merely claimed as supported by prose

- freebsd is not merely claimed as supported by prose
   - Expected: impl_present or selector_arm is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("freebsd is not merely claimed as supported by prose")
# EXPECTED RED. FreeBSD has zero seam arms anywhere: no backend file,
# no `freebsd` token in src/runtime/hosted/select.rs. Its only
# presence is two docstrings in hosted_input_backend.spl claiming
# support. Prose is not an implementation.
val prose = source_contains("src/os/compositor/hosted_input_backend.spl", "FreeBSD")
val impl_present = file_exists("src/os/compositor/hosted_backend_freebsd.spl")
val selector_arm = source_contains("src/runtime/hosted/select.rs", "freebsd")
if prose:
    expect(impl_present or selector_arm).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WM-HOST-PLATFORM-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d4e9450f1023fd27497ebd142f92d6420cd0b21b65e8076496468ebd184f4909`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4e9450f1023fd27497ebd142f92d6420cd0b21b65e8076496468ebd184f4909`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4e9450f1023fd27497ebd142f92d6420cd0b21b65e8076496468ebd184f4909`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/wm_host_platform/wm_host_false_success_guard_spec.spl
mirror: doc/06_spec/03_system/gui/wm_host_platform/wm_host_false_success_guard_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/gui/wm_host_platform/wm_host_false_success_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_host_platform/wm_host_false_success_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_host_platform/wm_host_false_success_guard_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/wm_host_platform/wm_host_false_success_guard_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'macos backend does not claim native cocoa symbols on a non-macos host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_host_false_success_guard_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'windows backend does not claim native win32 symbols on a non-windows host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_host_false_success_guard_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a backend claiming native symbols is gated by a real build feature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
