# Hosted Backend Dispatch Honesty — Cluster 0 (sites 0a-0d)

> Lane A1 of `doc/03_plan/ui/wm_platform_honesty_agent_lanes.md`. Cluster 0

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Backend Dispatch Honesty — Cluster 0 (sites 0a-0d)

Lane A1 of `doc/03_plan/ui/wm_platform_honesty_agent_lanes.md`. Cluster 0

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | Passing |
| Source | `test/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Lane A1 of `doc/03_plan/ui/wm_platform_honesty_agent_lanes.md`. Cluster 0
(`doc/04_architecture/ui/wm_host_platform_matrix.md` "False-success stubs,
ranked") is the dispatch/capability-self-report layer that sits above every
other WM host seam: a simulated host claiming to be native poisons every
consumer that trusts the claim. This spec locks the honest-refusal fix for
all four sites.

## Scope and Preconditions

- 0a/0b: `uses_native_cocoa_symbols()` / `uses_native_win32_symbols()` must
  reflect the real host (`is_macos()` / `is_windows()`, a genuine `uname -s`
  runtime probe), never a hardcoded literal.
- 0c: `HostedCompositorBackend.create()` must refuse (return `nil`) rather
  than fabricate a handle when there is no live winit backing.
- 0d: `HostedGuiRendererBackend.create()` must never return a backend whose
  pixel store length is 0 while reporting success.

## Recovery and Troubleshooting

A RED result here is a real regression toward false success, not a flaky
test — see the sabotage notes in the owning lane's report.

## Compatibility and Limitations

0a/0b runtime assertions are evaluated against the EXECUTING host (this
suite runs on Linux); the mac/win-true side of those two symbols is
static-only per the plan's platform-executability rule and is not claimed
green here.

## Scenarios

### 0a/0b — native-symbol self-reports reflect the real host

#### 0a: uses_native_cocoa_symbols() is false on this (non-macOS) host

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 0a: uses_native_cocoa_symbols() is false on this (non-macOS) host
   - Expected: HostedCocoaBackend.uses_native_cocoa_symbols() equals `host_os() == "macos"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("0a: uses_native_cocoa_symbols() is false on this (non-macOS) host")
expect(HostedCocoaBackend.uses_native_cocoa_symbols()).to_equal(host_os() == "macos")
```

</details>

#### 0b: uses_native_win32_symbols() is false on this (non-Windows) host

- 0b: uses_native_win32_symbols() is false on this (non-Windows) host
   - Expected: HostedWin32Backend.uses_native_win32_symbols() equals `host_os() == "windows"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("0b: uses_native_win32_symbols() is false on this (non-Windows) host")
expect(HostedWin32Backend.uses_native_win32_symbols()).to_equal(host_os() == "windows")
```

</details>

#### 0a-static: cocoa self-report body is not a hardcoded literal true

- 0a-static: cocoa self-report body is not a hardcoded literal true
   - Expected: body == "true" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("0a-static: cocoa self-report body is not a hardcoded literal true")
val body = first_body_statement("src/os/compositor/hosted_backend_cocoa.spl", "static fn uses_native_cocoa_symbols")
expect(body == "true").to_equal(false)
```

</details>

#### 0b-static: win32 self-report body is not a hardcoded literal true

- 0b-static: win32 self-report body is not a hardcoded literal true
   - Expected: body == "true" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("0b-static: win32 self-report body is not a hardcoded literal true")
val body = first_body_statement("src/os/compositor/hosted_backend_win32.spl", "static fn uses_native_win32_symbols")
expect(body == "true").to_equal(false)
```

</details>

### 0c — hosted winit buffer refuses instead of fabricating a handle

#### create() without a live window handle (window_id <= 0) returns nil

- create() without a live window handle (window_id <= 0) returns nil
   - Expected: backend equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("create() without a live window handle (window_id <= 0) returns nil")
val backend = HostedCompositorBackend.create(0, 100, 100, 0xFF000000)
expect(backend).to_equal(nil)
```

</details>

### 0d — gui-renderer create never reports success with an empty pixel store

#### refuses when the renderer is not open

- refuses when the renderer is not open
   - Expected: closed.is_open() is false
   - Expected: backend equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses when the renderer is not open")
val closed = GuiRenderer.empty()
expect(closed.is_open()).to_equal(false)
val backend = HostedGuiRendererBackend.create(closed, 4, 3, 0xFF000000)
expect(backend).to_equal(nil)
```

</details>

#### allocates a real w*h pixel store when it does report success

- allocates a real w*h pixel store when it does report success
   - Expected: fake.is_open() is true
   - Expected: backend != nil is true
   - Expected: backend.pixels.len() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allocates a real w*h pixel store when it does report success")
val fake = fake_open_renderer()
expect(fake.is_open()).to_equal(true)
val backend = HostedGuiRendererBackend.create(fake, 4, 3, 0xFF000000)
expect(backend != nil).to_equal(true)
if backend != nil:
    expect(backend.pixels.len()).to_equal(12)
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

- `REQ-SSPEC-SYSTEM`
- `REQ-WM-HOST-PLATFORM-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `095fb528c2fb6d4e5198711e001c56edf3c20a7faabce9b8f1157892e6e4a1bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `095fb528c2fb6d4e5198711e001c56edf3c20a7faabce9b8f1157892e6e4a1bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `095fb528c2fb6d4e5198711e001c56edf3c20a7faabce9b8f1157892e6e4a1bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.spl
mirror: doc/06_spec/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '0a: uses_native_cocoa_symbols() is false on this (non-macOS) host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '0b: uses_native_win32_symbols() is false on this (non-Windows) host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/hosted_backend_honesty_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '0a-static: cocoa self-report body is not a hardcoded literal true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
