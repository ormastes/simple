# Engine2D Backend Provenance Matrix Specification

> Keeps requested, actual, native, translated, emulated, and unavailable backend

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Backend Provenance Matrix

Keeps requested, actual, native, translated, emulated, and unavailable backend

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Keeps requested, actual, native, translated, emulated, and unavailable backend
states honest through the real Engine2D facade.

## Scenarios

### Engine2D backend provenance matrix

#### labels DirectX and Metal requests translated onto Vulkan

- labels DirectX and Metal requests translated onto Vulkan
- Request DirectX and Metal compatibility lanes
   - Expected: directx.backend_name() equals `directx-on-vulkan`
   - Expected: directx_readback.source equals `device_readback`
   - Expected: directx_readback.pixel_count equals `32`
   - Expected: metal.backend_name() equals `metal-on-vulkan`
   - Expected: metal_readback.source equals `device_readback`
   - Expected: metal_readback.pixel_count equals `32`
   - Expected: metal_readback.pixels equals `directx_pixels`
   - Expected: metal_readback.checksum equals `directx_checksum`

#### keeps native Windows and macOS checkpoints honest on Linux

On Linux, the DirectX request may only report
`directx-software-emulation`; strict Metal must remain unavailable and retain
the requested backend identity. Other hosts retain a nonempty platform name.

#### rejects CPU fallback from a backend-specific pass

An unknown strict backend must return a typed diagnostic whose requested name
is unchanged and whose selected name is not `cpu`.

<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("labels DirectX and Metal requests translated onto Vulkan")
step("Request DirectX and Metal compatibility lanes")
var directx_pixels: [u32] = []
var directx_checksum: i64 = 0
match Engine2D.create_requested_backend(8, 4, "directx-on-vulkan"):
    Err(reason): expect(reason.len()).to_be_greater_than(0)
    Ok(directx):
        expect(directx.backend_name()).to_equal("directx-on-vulkan")
        directx.clear(0xff102030u32)
        directx.draw_rect_filled(2, 1, 4, 2, 0xffa0b0c0u32)
        directx.present()
        val directx_readback = directx.read_pixels_with_source()
        expect(directx_readback.source).to_equal("device_readback")
        expect(directx_readback.backend_handle).to_be_greater_than(0)
        expect(directx_readback.device_identity).to_be_greater_than(0)
        expect(directx_readback.pixel_count).to_equal(32)
        expect(directx_readback.checksum).to_be_greater_than(0)
        directx_pixels = directx_readback.pixels
        directx_checksum = directx_readback.checksum
        directx.shutdown()
match Engine2D.create_requested_backend(8, 4, "metal-on-vulkan"):
    Err(reason): expect(reason.len()).to_be_greater_than(0)
    Ok(metal):
        expect(metal.backend_name()).to_equal("metal-on-vulkan")
        metal.clear(0xff102030u32)
        metal.draw_rect_filled(2, 1, 4, 2, 0xffa0b0c0u32)
        metal.present()
        val metal_readback = metal.read_pixels_with_source()
        expect(metal_readback.source).to_equal("device_readback")
        expect(metal_readback.backend_handle).to_be_greater_than(0)
        expect(metal_readback.device_identity).to_be_greater_than(0)
        expect(metal_readback.pixel_count).to_equal(32)
        expect(metal_readback.checksum).to_be_greater_than(0)
        if directx_pixels.len() > 0:
            expect(metal_readback.pixels).to_equal(directx_pixels)
            expect(metal_readback.checksum).to_equal(directx_checksum)
        metal.shutdown()

</details>

<details>
<summary>Advanced: keeps native Windows and macOS checkpoints honest on Linux</summary>

#### keeps native Windows and macOS checkpoints honest on Linux

- keeps native Windows and macOS checkpoints honest on Linux
- Inspect native D3D and Metal host checkpoints
   - Expected: directx.backend_name() equals `directx-software-emulation`
   - Expected: metal.unwrap_err().requested_name equals `metal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps native Windows and macOS checkpoints honest on Linux")
step("Inspect native D3D and Metal host checkpoints")
if detect_os() == "linux":
    match Engine2D.create_requested_backend(4, 4, "directx"):
        Err(reason): expect(reason.len()).to_be_greater_than(0)
        Ok(directx):
            expect(directx.backend_name()).to_equal("directx-software-emulation")
            directx.shutdown()
    val metal = Engine2D.create_with_backend_strict(4, 4, "metal")
    expect(metal.is_ok()).to_be(false)
    expect(metal.unwrap_err().requested_name).to_equal("metal")
else:
    expect(detect_os().len()).to_be_greater_than(0)

</details>


</details>

<details>
<summary>Advanced: rejects CPU fallback from a backend-specific pass</summary>

#### rejects CPU fallback from a backend-specific pass

- rejects CPU fallback from a backend-specific pass
- Request an unavailable backend through the strict facade
   - Expected: diagnostic.requested_name equals `does-not-exist`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects CPU fallback from a backend-specific pass")
step("Request an unavailable backend through the strict facade")
val result = Engine2D.create_with_backend_strict(4, 4, "does-not-exist")
expect(result.is_ok()).to_be(false)
val diagnostic = result.unwrap_err()
expect(diagnostic.requested_name).to_equal("does-not-exist")
expect(diagnostic.selected_name == "cpu").to_be(false)
```


Reproduction: the executable source is
`test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl`.
It uses only `Engine2D.create_requested_backend`,
`Engine2D.create_with_backend_strict`, draw/present, and
`read_pixels_with_source`; no fixture backend or middle mock is involved.

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Integration |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl` |
| Updated | 2026-07-27 |
| Generator | Manual synchronization while the self-hosted checker crash is open |

## Coverage Boundary

Physical NVIDIA/AMD/Intel versus lavapipe qualification requires separate
ICD-selected external runs and is tracked in the external-host TODO. This
integration spec validates translation, native/emulated naming, strict
unavailability, and fallback rejection without pretending one process ran two
devices.

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

- `REQ-SSPEC-INTEGRATION`
- `REQ-005`
- `REQ-007`
- `REQ-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9742926eb65356fd05ae6c5e353d2ef0de457ec2cfa2d69c75f67038c569356a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9742926eb65356fd05ae6c5e353d2ef0de457ec2cfa2d69c75f67038c569356a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9742926eb65356fd05ae6c5e353d2ef0de457ec2cfa2d69c75f67038c569356a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl
mirror: doc/06_spec/02_integration/rendering/engine2d_backend_provenance_matrix_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/02_integration/rendering/engine2d_backend_provenance_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/engine2d_backend_provenance_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'labels DirectX and Metal requests translated onto Vulkan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps native Windows and macOS checkpoints honest on Linux' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects CPU fallback from a backend-specific pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
