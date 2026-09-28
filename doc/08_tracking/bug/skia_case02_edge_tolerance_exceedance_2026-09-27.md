# Skia case02: 4 edge pixels exceed the predeclared 16-channel-delta tolerance

- **Filed:** 2026-09-27
- **Class:** measured rasterizer deviation vs predeclared analytic tolerance
- **Status:** open — needs an owner decision (see "Decision needed")

## Measured evidence (macOS M4, MoltenVK 1.4.1, admitted device)

The pinned upstream Skia Ganesh Vulkan provider (`build/optional/
libsimple_upstream_skia_ganesh_vulkan_v3.dylib`, receipt
`affine_v3_enabled=1`, provider sha256 `ffe83312…`) rendered the DrawIR v4
case02 projection (4 white clears + rotated tile + fractional bar) from an
exact replica of the adapter's v3 wire format. Submitted-matrix provenance was
recorded: source f64 (a=0.99254615164132198, b=0.12186934340514748, c=-b,
d=a, tx=47.266176984628068, ty=40.123984175619334), submitted f32, max
transformed-corner error 0.000434 px against the predeclared 0.125 px bound.

Independent analytic area oracle (C port of
`src/lib/common/renderdoc/corpus_case02_polygon_oracle.spl`):

| metric | measured | predeclared bound |
|---|---|---|
| interior/exterior exact mismatches | 0 | 0 |
| bar regions (interior/edge) | 558 / 285 | 558 / 285 (exact) |
| edge mean channel delta | 0.0149 | ≤ 4 |
| edge pixels over 16-channel delta | **4 of 914** | 0 |
| edge max channel delta | **30** | ≤ 16 |
| tile interior/edge region counts | 17644 / 715 | 17730 / 629 |

Probe source and full log: `build/optional/skia_case02_probe.c`,
`build/optional/skia_case02_probe_run1.log`. Verdict `passed=0`.

## Interpretation

Skia's coverage-AA treatment of the rotated tile's edges deviates from the
ideal per-pixel area model on 4 pixels (max ≈12% coverage difference) and
moves 86 pixels across the ideal full/partial boundary. Interior, exterior,
and the untransformed fractional bar are exact; edge mean is two orders of
magnitude inside the bound. This is rasterizer-specific edge policy, not a
transform or clip-ordering defect (submitted-matrix provenance is clean and
the clip is full-surface).

## Decision needed

Either (a) the predeclared case02 tolerance should accommodate documented
rasterizer edge policy (e.g. a small allowed excess-pixel count, as real GPU
rasterizers are not ideal area samplers), or (b) the v3 execution sequence in
`provider.cpp` should align coverage with the area model more closely. Until
then, case02 remains FAIL on the Skia backend under the pinned comparator,
and this row must not be reported as PASS.

Related: the default (non-v3) provider rejects the v3 payload with REJECTED
before GPU work — device-verified on both builds; v1/v2 scenes (case01,
case06) match their pinned oracles exactly on both builds.
