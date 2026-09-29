# WM/GUI Host Seam — Per-Platform Presence and Trait Completeness

> Verifies that each of the five target platforms supplies an implementation of

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM/GUI Host Seam — Per-Platform Presence and Trait Completeness

Verifies that each of the five target platforms supplies an implementation of

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/gui/wm_host_platform/wm_host_seam_presence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Verifies that each of the five target platforms supplies an implementation of
the 2D-surface host seam, and that the implementation is COMPLETE — every
seam method really implemented, not a partial class that happens to compile.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Seam | `trait CompositorBackend`, 11 methods, `display_backend_core.spl` |
| Completeness proof | Simple refuses to compile an incomplete `impl Trait for T` block. Therefore successfully importing a platform backend module and resolving a symbol from it is a positive, compiler-enforced proof that the `impl CompositorBackend` block implements all 11 methods. This is stronger than grepping for method names, which cannot tell a real body from a signature. |
| Tier | See `wm_host_evidence_tier_spec.spl`. Presence and completeness are STATIC properties and are legitimately checkable from any host; they make no runtime claim. |

## Compatibility and Limitations

Every check in this file is static. Passing here does NOT mean the platform's
seam runs — see `wm_host_runtime_linux_spec.spl` for the only runtime claim
this host can make, and the evidence-tier ledger for why.

## Scenarios

### WM host seam — declaration

#### declares the canonical 2D-surface seam trait

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- declares the canonical 2D-surface seam trait
   - Expected: file_exists(SEAM_TRAIT_FILE) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares the canonical 2D-surface seam trait")
expect(file_exists(SEAM_TRAIT_FILE)).to_equal(true)
```

</details>

#### declares eleven seam methods

- declares eleven seam methods
   - Expected: seam_methods().len() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares eleven seam methods")
expect(seam_methods().len()).to_equal(11)
```

</details>

### WM host seam — per-platform implementation is present

#### linux supplies a seam implementation

- linux supplies a seam implementation
   - Expected: file_exists(seam_impl_path("linux")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("linux supplies a seam implementation")
expect(file_exists(seam_impl_path("linux"))).to_equal(true)
```

</details>

#### macos supplies a seam implementation

- macos supplies a seam implementation
   - Expected: file_exists(seam_impl_path("macos")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("macos supplies a seam implementation")
expect(file_exists(seam_impl_path("macos"))).to_equal(true)
```

</details>

#### windows supplies a seam implementation

- windows supplies a seam implementation
   - Expected: file_exists(seam_impl_path("windows")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("windows supplies a seam implementation")
expect(file_exists(seam_impl_path("windows"))).to_equal(true)
```

</details>

#### simpleos supplies a seam implementation

- simpleos supplies a seam implementation
   - Expected: file_exists(seam_impl_path("simpleos")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("simpleos supplies a seam implementation")
expect(file_exists(seam_impl_path("simpleos"))).to_equal(true)
```

</details>

#### freebsd supplies a seam implementation

- freebsd supplies a seam implementation
   - Expected: file_exists(seam_impl_path("freebsd")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("freebsd supplies a seam implementation")
# EXPECTED RED. There is no `hosted_backend_freebsd.spl`, no
# `freebsd` arm in `src/runtime/hosted/select.rs`, and no FreeBSD
# case anywhere in the seam dispatch. FreeBSD silently rides the
# winit fallback while two docstrings in
# `src/os/compositor/hosted_input_backend.spl` claim support.
# The portability contract says every platform implements the seam;
# FreeBSD does not. This must read as MISSING, not as a quiet pass.
expect(file_exists(seam_impl_path("freebsd"))).to_equal(true)
```

</details>

### WM host seam — per-platform implementation is complete

#### linux seam impl compiles complete and self-identifies

- linux seam impl compiles complete and self-identifies
   - Expected: HostedWinitBufferBackend.implementation_name() equals `simple-2d-winit-buffer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("linux seam impl compiles complete and self-identifies")
expect(HostedWinitBufferBackend.implementation_name()).to_equal("simple-2d-winit-buffer")
```

</details>

#### macos seam impl compiles complete and self-identifies

- macos seam impl compiles complete and self-identifies
   - Expected: HostedCocoaBackend.implementation_name() equals `cocoa-real-sffi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("macos seam impl compiles complete and self-identifies")
expect(HostedCocoaBackend.implementation_name()).to_equal("cocoa-real-sffi")
```

</details>

#### windows seam impl compiles complete and self-identifies

- windows seam impl compiles complete and self-identifies
   - Expected: HostedWin32Backend.implementation_name() equals `win32-native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("windows seam impl compiles complete and self-identifies")
expect(HostedWin32Backend.implementation_name()).to_equal("win32-native")
```

</details>

#### headless seam impl compiles complete

- headless seam impl compiles complete
   - Expected: b.width() equals `8`
   - Expected: b.height() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("headless seam impl compiles complete")
val b = HeadlessHostCompositorBackend.new(8, 4)
expect(b.width()).to_equal(8)
expect(b.height()).to_equal(4)
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
- `REQ-WM-HOST-PLATFORM-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c163a50f35805c233e80ac3f50bea963d4d8d4ad1e69ece7ea18e390d294d96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c163a50f35805c233e80ac3f50bea963d4d8d4ad1e69ece7ea18e390d294d96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c163a50f35805c233e80ac3f50bea963d4d8d4ad1e69ece7ea18e390d294d96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/wm_host_platform/wm_host_seam_presence_spec.spl
mirror: doc/06_spec/03_system/gui/wm_host_platform/wm_host_seam_presence_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/gui/wm_host_platform/wm_host_seam_presence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_host_platform/wm_host_seam_presence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_host_platform/wm_host_seam_presence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/wm_host_platform/wm_host_seam_presence_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/wm_host_platform/wm_host_seam_presence_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares the canonical 2D-surface seam trait' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_host_seam_presence_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares eleven seam methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_host_seam_presence_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'linux supplies a seam implementation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
