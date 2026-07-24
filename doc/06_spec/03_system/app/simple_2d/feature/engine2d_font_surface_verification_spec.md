# Engine2D Font Surface Verification

> Canonical manual mirror for
> `test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl`.

| Scenarios | Active | Passed now | Blocked now |
|---|---:|---:|---:|
| CPU / `cpu_simd` compatibility | 1 | 0 | 1 |
| Vulkan device readback | 1 | 0 | 1 |

## Status

**BLOCKED — no current pure-Simple execution receipt or retained framebuffer
captures exist for this specification.**

The source spec defines the required absolute oracles, but this documentation-
only update did not run docgen, the test runner, a native build, or a graphics
device. Nothing in this manual upgrades an unexecuted row to PASS.

## Purpose

This scenario drives the public `Engine2D.create_requested_backend` facade with:

- the pinned Noto Sans Mono asset;
- the semantic text `Simple 2D`;
- a 128×72 packed-ARGB framebuffer;
- an exact CPU pixel oracle;
- a requested `cpu_simd` compatibility lane;
- a requested Vulkan device lane.

The captured artifact directory, when a future run succeeds, is:

```text
build/test-artifacts/03_system/app/simple_2d/feature/
└── engine2d_font_surface_verification/
    ├── cpu.argb
    ├── cpu_simd.argb
    └── vulkan.argb
```

Artifact names describe requests, not proof. `cpu_simd.argb` is not evidence of
SIMD execution unless separate native SIMD provenance exists. `vulkan.argb` is
not Vulkan proof unless the scenario also observes device-origin readback and
positive device handles.

## Capability Truth Table

| Row | Required observation | Current truth |
|---|---|---|
| CPU oracle | backend `cpu`, source `cpu_mirror`, execution target `cpu`, exact 9,216 pixels | **BLOCKED: not executed** |
| `cpu_simd` request | backend label `cpu_simd`, source `cpu_mirror`, execution target `cpu`, exact CPU parity | **BLOCKED: not executed; compatibility contract only** |
| Real SIMD execution | native SIMD target/provenance and independently attributable SIMD work | **BLOCKED: this spec supplies no such proof** |
| Vulkan | backend and execution target `vulkan`, `device_readback`, positive backend handle and device identity, exact CPU parity | **BLOCKED: no device execution receipt** |

### CPU compatibility is not SIMD proof

The `cpu_simd` scenario deliberately expects:

```text
backend=cpu_simd
source=cpu_mirror
execution_target=cpu
attempts contains cpu:success
```

That row proves only that a `cpu_simd` request preserves CPU-rendered pixels
while honestly disclosing CPU execution. It must never be reported as native
SIMD acceleration, SIMD device readback, or SIMD performance evidence.

### Vulkan naming is not device proof

The Vulkan scenario fails unless all of these facts hold together:

```text
backend=vulkan
execution_target=vulkan
source=device_readback
backend_handle>0
device_identity>0
vulkan_pixels==cpu_pixels
```

A software fallback, CPU mirror, emitted shader, backend-name relabel, upload-
only receipt, or unavailable Vulkan device remains BLOCKED.

## Primary Flow

The shared font flow uses the repository’s frozen operator vocabulary.

1. **Load the pinned multilingual font manifest**
   - Hash
     `assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf`.
   - Require SHA-256
     `2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.
   - Bind the semantic text exactly as `Simple 2D`.

2. **Accept exact-face-bound simple-script shaping**
   - Request the CPU reference surface.
   - Require CPU backend and `cpu_mirror` provenance.
   - Require the font execution attempt to end in `cpu:success`.

3. **Prepare one shared font batch for 2D and 3D**
   - Request either `cpu_simd` or `vulkan` through the same Engine2D facade.
   - Do not introduce another renderer, atlas, cache, or private font path.
   - Treat the `cpu_simd` request as CPU compatibility until native SIMD
     provenance exists.

4. **Emit the selected font composite program and plan compilation**
   - Compare the complete requested framebuffer with the CPU framebuffer.
   - Require equality of every packed-ARGB pixel; checksums and tolerances are
     insufficient.

5. **Prove native submission and device readback**
   - Require 9,216 pixels and a nonempty antialiased glyph region.
   - Retain the exact ARGB capture.
   - For Vulkan, additionally require device readback and positive native
     handles.
   - For `cpu_simd`, continue to report CPU compatibility unless real SIMD
     execution is proved elsewhere.

## Scenario 1: CPU / `cpu_simd` Compatibility

**User-visible outcome:** the `cpu_simd` request produces the exact CPU glyph
frame while disclosing that font execution remained on CPU.

Absolute assertions:

- framebuffer length is `128 * 72`;
- at least one pixel differs from background;
- at least one partially covered antialias pixel exists;
- painted count and partial count equal the CPU oracle;
- minimum and maximum painted bounds equal the CPU oracle;
- glyph bounds remain inside the framebuffer;
- all 9,216 pixels equal the CPU oracle;
- `cpu.argb` and `cpu_simd.argb` are retained only after those assertions.

**Current result: BLOCKED.** No runner result or capture was produced in this
documentation-only follow-up.

## Scenario 2: Vulkan Device Readback

**User-visible outcome:** Vulkan produces the same absolute glyph frame only
after real device submission and readback.

Absolute assertions:

- backend and font execution target both equal `vulkan`;
- attempts include a Vulkan attempt;
- all pixels equal the CPU oracle;
- readback source equals `device_readback`;
- backend handle and device identity are positive;
- painted count, partial count, and glyph bounds equal CPU;
- `vulkan.argb` is retained only after those assertions.

**Current result: BLOCKED.** No current Vulkan device receipt or capture exists.
Unavailable Vulkan must fail the scenario; it is never converted to PASS.

## Operator Command

Run only with the pure-Simple self-hosted binary:

```bash
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_LIB=src \
bin/release/x86_64-unknown-linux-gnu/simple test \
test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl \
--mode=native
```

Before accepting evidence, record the resolved binary path, version, SHA-256,
exit code, retained ARGB paths, selected backend, execution target, readback
source, backend handle, and device identity.

## Pass and Block Rules

PASS requires both requested rows to satisfy their own assertions in a current
run. The `cpu_simd` row may pass only as CPU compatibility under its present
contract; it does not satisfy a claim of real SIMD execution.

The feature remains BLOCKED when any of these is true:

- the pure-Simple runner was not executed;
- zero scenarios executed;
- the font hash differs;
- `cpu_simd` is described as native SIMD without native provenance;
- Vulkan is unavailable;
- Vulkan uses `cpu_mirror`;
- either Vulkan handle is zero;
- any requested framebuffer pixel differs from CPU;
- a retained capture is missing.

## Traceability

- Requirements: AC-1, AC-6, AC-7, AC-8, AC-9
- Executable spec:
  `test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl`
- Font implementation owner: `FontRenderer` and transient `FontRenderBatch`
- Composition owner: `DrawIrComposition`
- Text execution owner: Engine2D `draw_text`
- Current documentation status: manual present, execution BLOCKED
