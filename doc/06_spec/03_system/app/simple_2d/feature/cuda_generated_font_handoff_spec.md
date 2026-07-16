# CUDA Generated Font Handoff

**Status:** conditional supporting evidence; release-blocking only when CUDA is selected
**Traceability:** REQ-010, REQ-014; NFR-002, NFR-008
**Executable:** `test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl`

> Hand-maintained mirror pending canonical `spipe-docgen`; no generated-manual
> PASS is claimed.

This focused scenario proves only the generated CUDA Engine2D font-composite
handoff. It is independent of the Vulkan Engine3D, SimpleOS framebuffer, and
performance rows in `native_gpu_font_readback_spec.spl`; those rows need not use
the same device or backend.

## Operator flow

### Prove native submission and device readback

Run `sh scripts/check/check-portable-compute-toolchains.shs` with a fresh pure-Simple compiler,
its resolved native runtime, `nvcc`, and an explicit device-supported
`CUDA_ARCH`. Point `CUDA_FONT_TOOLCHAIN_EVIDENCE` at the resulting
`evidence.env`, then execute this one-scenario spec.

The retained record must contain exact SHA-256 identities for the Simple
invocation and resolved native runtime, current font-emitter source/version,
the retained generated `.cu`, and the compiled PTX. The scenario recomputes the
current CUDA font emitter hashes, compares the retained source content and file
hash, verifies both Simple binaries are unchanged, and requires the versioned
`simple_font_atlas_composite_v1_u32` export.

It then installs the PTX through `Engine2D.install_cuda_font_artifact`, submits
one canonical 1×1 `FontRenderBatch` through CUDA only, captures the pinned
module identity before shutdown, and requires `cuda:success`, a nonzero device
readback handle, and exact equality with the 4×4 CPU pixel oracle. Missing or
stale provenance, fallback rendering, an unavailable CUDA device, or a pixel
mismatch fails explicitly.

The default CUDA 2D module has no font entry. Without the verified generated
companion, normal Engine2D policy records CUDA failure and replays from quad
zero on CPU; a CUDA-required evidence row fails rather than accepting fallback.

This scenario authenticates retained checker provenance for conditional native
evidence; it does not prove production packaging. The checker-recorded hash is
payload consistency metadata, not an independent package trust anchor.
Production completion additionally requires an immutable package-owned expected
hash/program-version binding, checksum verification before installation, tamper
rejection, and the same device-readback proof using authenticated package bytes.
Normal Engine2D creation must not discover the files listed below automatically.

## Evidence artifacts

- `build/portable_compute_toolchains/evidence.env`
- `build/portable_compute_toolchains/simple_2d_optimization_font_atlas.cu`
- `build/portable_compute_toolchains/simple_2d_optimization_font_atlas.ptx`
- checker compiler/emitter logs and the focused SPipe result

The executable spec is authoritative. Regenerate this manual after its single
scenario passes and require SPipe docgen to report zero stubs.
