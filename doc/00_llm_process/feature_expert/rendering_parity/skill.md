# Feature Expert — Rendering parity (comparator, adapters, retained diagnostics)

## Role

Own process knowledge for proving that two rendering lanes (Chrome reference,
Simple CPU/SIMD/GPU, Simple Web) produce the same pixels. Every verdict comes
from one exact comparator; adapters only canonicalize a backend's output.

## Pipeline Links

- Comparator and contracts: `src/lib/common/ui/rendering_parity.spl`
- Specs: `test/01_unit/lib/common/ui/rendering_parity/`
- Engine2D adapter: `src/lib/gc_async_mut/gpu/engine2d/rendering_parity_adapter.spl`
- Simple Web adapter: `src/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter.spl`
- Retained mismatch diagnostics: `src/app/test/chrome_component_renderer_parity/diagnostics.spl`
  (spec `test/01_unit/app/test/chrome_component_renderer_parity/diagnostics_spec.spl`)

## Comparator (`common.ui.rendering_parity`)

1. Pixels are straight RGBA8, top-left origin, sRGB. `pixel_format_descriptor`,
   `argb_u32_to_straight_rgba8` and `byte_pixels_to_straight_rgba8` convert
   ARGB words / BGRA / premultiplied / bottom-left input; stride is validated.
2. `compare_rgba8_with_policy` accepts the `exact` policy only. Channel
   tolerance is legal solely via `compare_rgba8_for_fixture`, where the policy id
   (`fixture:<id>`) and bounds must equal what the `RenderingFixture` declares
   (`rendering_fixture_with_tolerance`). Never invent a tolerance in a caller.
3. `compare_rgba8_with_policy_and_diagnostics` /
   `compare_rgba8_for_fixture_with_diagnostics` attach evidence paths and a
   reproduction command to `RenderComparison.diagnostic` (mismatch count,
   bounding box, max channel delta); empty paths are an error.
4. A blank actual against a non-blank expected is its own failure
   (`rgba8_is_blank`, `rgba8_has_visible_diversity`).
5. Stage records (`rendering_stage_record_v1`) must be in stage order
   (`rendering_stage_records_valid_order`); `compare_rendering_stages` reports the
   first divergent stage.
6. `backend_evidence_v1` carries truthful physical-GPU / software / CPU-fallback /
   simulated flags; `backend_evidence_distinct_execution` rejects two rows that
   share one execution.
7. `CanonicalRenderOutput` (field `rgba8`) is built by `canonical_render_output`
   (no stages, `not_run` evidence) or `canonical_render_output_v1`, which also
   requires ordered stage records, evidence matching case/backend/size and a
   non-empty source artifact. Checksum is `stable_bytes_checksum` over the bytes.

## Adapters

- Engine2D: `engine2d_rendering_parity_backend_name` maps manifest rows
  (`simple_cpu`->cpu, `simple_simd`->cpu_simd, `simple_gpu`->a physical API; a GPU
  row never silently maps to CPU). `..._canonicalize` converts the readback,
  `..._evidence` builds truthful evidence, `..._not_run` records an unsupported
  lane, and `..._execute_composition` renders a DrawIr composition and appends
  the raster stage. The CPU raster is straight alpha (`ENGINE2D_CPU_ALPHA_MODE`).
- Simple Web: `simple_web_rendering_parity_stage_records`, `..._render_rgba8`
  and `..._check` render an HTML fixture on the software browser renderer and
  compare with the exact comparator.

## Packed composition owner (DrawIr v3)

Compositions flow as `DrawIrComposition` through the packed DrawIr v3 owner
(`src/lib/common/ui/draw_ir_v3.spl`, backend access in
`draw_ir_v3_backend_access.spl`, v2 bridge in `draw_ir_v2_to_v3.spl`). v3 is
frozen/read-only for parity lanes: adapters consume it, they do not extend it.

## Retained diagnostics (Chrome component lane)

On a mismatch `write_parity_mismatch_artifacts` writes
`<root>/<fixture>/{expected,actual,diff}.rgba8` (diff = absolute per-byte
difference) and `summary.sdn` (box, delta, converter `id@version`, checksums,
repro command). `validate_parity_mismatch_artifacts` re-derives everything and
fails closed on any changed byte or receipt. Fixture/row ids with path
separators or `..` and equal comparisons are rejected without publishing.

## Gotchas

- Run specs with `bin/simple test --no-session-daemon <spec>`; non-`pub` fns of
  `rendering_parity.spl` make the JIT demote to the interpreter (results still
  real).
- The rest of `app.test.chrome_component_renderer_parity` (runner, manifest,
  cache, report, ...) is still missing; sibling specs there do not run yet.
