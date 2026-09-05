# Hosted SDL2 Backend Spec

> Unit tests for the SDL2 compositor backend. Tests use the headless

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted SDL2 Backend Spec

Unit tests for the SDL2 compositor backend. Tests use the headless

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/compositor/hosted_backend_sdl2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the SDL2 compositor backend. Tests use the headless
fallback path since rt_sdl2_* externs return stubs in test mode.

## Scenarios

### HostedSdl2Backend

#### reports sdl2-native as implementation name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports sdl2-native as implementation name
   - Expected: HostedSdl2Backend.implementation_name() equals `sdl2-native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports sdl2-native as implementation name")
expect(HostedSdl2Backend.implementation_name()).to_equal("sdl2-native")
```

</details>

#### rejects zero-width creation

- rejects zero-width creation
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero-width creation")
val result = HostedSdl2Backend.try_create(0, 480, "test")
expect(result).to_equal(nil)
```

</details>

#### rejects zero-height creation

- rejects zero-height creation
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero-height creation")
val result = HostedSdl2Backend.try_create(640, 0, "test")
expect(result).to_equal(nil)
```

</details>

#### rejects negative dimensions

- rejects negative dimensions
   - Expected: result equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative dimensions")
val result = HostedSdl2Backend.try_create(-1, -1, "test")
expect(result).to_equal(nil)
```

</details>

#### clear/fill_rect/put_pixel update the CPU pixel buffer directly

- clear/fill_rect/put_pixel update the CPU pixel buffer directly
   - Expected: be.read_pixel(0, 0) equals `0xAABBCCDDu32`
   - Expected: be.read_pixel(1, 1) equals `0x11223344u32`
   - Expected: be.read_pixel(3, 3) equals `0x99999999u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear/fill_rect/put_pixel update the CPU pixel buffer directly")
val be = HostedSdl2Backend(window_handle: 0, w: 4, h: 4, pixels: [0u32; 16])
be.clear(0xAABBCCDDu32)
expect(be.read_pixel(0, 0)).to_equal(0xAABBCCDDu32)
be.fill_rect(1, 1, 2, 2, 0x11223344u32)
expect(be.read_pixel(1, 1)).to_equal(0x11223344u32)
be.put_pixel(3, 3, 0x99999999u32)
expect(be.read_pixel(3, 3)).to_equal(0x99999999u32)
```

</details>

#### resize() refuses on a dead window handle instead of reporting fake success

- resize() refuses on a dead window handle instead of reporting fake success
   - Expected: be.resize(8, 8) is false
   - Expected: be.width() equals `4`
   - Expected: be.height() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resize() refuses on a dead window handle instead of reporting fake success")
val be = HostedSdl2Backend(window_handle: 0, w: 4, h: 4, pixels: [0u32; 16])
expect(be.resize(8, 8)).to_equal(false)
expect(be.width()).to_equal(4)
expect(be.height()).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da2f376315e0b621f374496d25f878b5c6d4277c925b1598ff35a71f1dcfac6a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da2f376315e0b621f374496d25f878b5c6d4277c925b1598ff35a71f1dcfac6a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da2f376315e0b621f374496d25f878b5c6d4277c925b1598ff35a71f1dcfac6a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/compositor/hosted_backend_sdl2_spec.spl
mirror: doc/06_spec/unit/os/compositor/hosted_backend_sdl2_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/compositor/hosted_backend_sdl2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/compositor/hosted_backend_sdl2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/compositor/hosted_backend_sdl2_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/compositor/hosted_backend_sdl2_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports sdl2-native as implementation name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/compositor/hosted_backend_sdl2_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects zero-width creation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/compositor/hosted_backend_sdl2_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects zero-height creation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
