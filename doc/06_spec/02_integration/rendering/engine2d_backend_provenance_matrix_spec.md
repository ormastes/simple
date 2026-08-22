# Engine2D Backend Provenance Matrix

> Verifies the engine2d backend provenance matrix behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Backend Provenance Matrix

Verifies the engine2d backend provenance matrix behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the engine2d backend provenance matrix behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Engine2D backend provenance matrix

#### labels DirectX and Metal requests translated onto Vulkan

- Verify: labels DirectX and Metal requests translated onto Vulkan
- Request DirectX and Metal compatibility lanes
   - Expected: directx.backend_name() equals `directx-on-vulkan`
   - Expected: directx_readback.source equals `device_readback`
   - Expected: directx_readback.pixel_count equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: metal.backend_name() equals `metal-on-vulkan`
   - Expected: metal_readback.source equals `device_readback`
   - Expected: metal_readback.pixel_count equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: metal_readback.pixels equals `directx_pixels`
   - Expected: metal_readback.checksum equals `directx_checksum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-007 REQ-008
step("Verify: labels DirectX and Metal requests translated onto Vulkan")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Request DirectX and Metal compatibility lanes")
var directx_pixels: [u32] = []
var directx_checksum: i64 = 0
match Engine2D.create_requested_backend(8, 4, "directx-on-vulkan"):
    Err(reason): expect(reason.len()).to_be_greater_than(0)
    Ok(directx):
        expect(directx.backend_name()).to_equal("directx-on-vulkan")
        directx.clear(0xff102030u32)
        directx.draw_rect_filled(2, 1, 4, 2, 0xffa0b0c0u32)
        # Read BEFORE present(): the dirty-frame path downloads pixels
        # straight from the device buffer (source=device_readback);
        # present() refreshes the host cache and a later read would be
        # honestly labeled host_cache_after_device_copy instead.
        val directx_readback = directx.read_pixels_with_source()
        expect(directx_readback.source).to_equal("device_readback")
        expect(directx_readback.backend_handle).to_be_greater_than(0)
        expect(directx_readback.device_identity).to_be_greater_than(0)
        expect(directx_readback.pixel_count).to_equal(32)  # oracle: pinned constant asserted by this scenario
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
        # Read BEFORE present() — same device_readback provenance rule
        # as the DirectX lane above.
        val metal_readback = metal.read_pixels_with_source()
        expect(metal_readback.source).to_equal("device_readback")
        expect(metal_readback.backend_handle).to_be_greater_than(0)
        expect(metal_readback.device_identity).to_be_greater_than(0)
        expect(metal_readback.pixel_count).to_equal(32)  # oracle: pinned constant asserted by this scenario
        expect(metal_readback.checksum).to_be_greater_than(0)
        if directx_pixels.len() > 0:
            expect(metal_readback.pixels).to_equal(directx_pixels)
            expect(metal_readback.checksum).to_equal(directx_checksum)
        metal.shutdown()
```

</details>

<details>
<summary>Advanced: keeps native Windows and macOS checkpoints honest on Linux</summary>

#### keeps native Windows and macOS checkpoints honest on Linux

- Verify: keeps native Windows and macOS checkpoints honest on Linux
- Inspect native D3D and Metal host checkpoints
   - Expected: directx.backend_name() equals `directx-software-emulation`
   - Expected: metal.unwrap_err().requested_name equals `metal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-007 REQ-008
step("Verify: keeps native Windows and macOS checkpoints honest on Linux")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
```

</details>


</details>

<details>
<summary>Advanced: rejects CPU fallback from a backend-specific pass</summary>

#### rejects CPU fallback from a backend-specific pass

- Verify: rejects CPU fallback from a backend-specific pass
- Request an unavailable backend through the strict facade
   - Expected: diagnostic.requested_name equals `does-not-exist`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-007 REQ-008
step("Verify: rejects CPU fallback from a backend-specific pass")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Request an unavailable backend through the strict facade")
val result = Engine2D.create_with_backend_strict(4, 4, "does-not-exist")
expect(result.is_ok()).to_be(false)
val diagnostic = result.unwrap_err()
expect(diagnostic.requested_name).to_equal("does-not-exist")
expect(diagnostic.selected_name == "cpu").to_be(false)
```

</details>


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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d59b9461da10ae3c7ea45815005ddab584ee69266839e519b4d741801278b223`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d59b9461da10ae3c7ea45815005ddab584ee69266839e519b4d741801278b223`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d59b9461da10ae3c7ea45815005ddab584ee69266839e519b4d741801278b223`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl
mirror: doc/06_spec/02_integration/rendering/engine2d_backend_provenance_matrix_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/engine2d_backend_provenance_matrix_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/rendering/engine2d_backend_provenance_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/engine2d_backend_provenance_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
