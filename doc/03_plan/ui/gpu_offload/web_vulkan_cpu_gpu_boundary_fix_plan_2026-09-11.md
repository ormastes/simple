# Web/2D Vulkan CPU<->GPU boundary fix plan (2026-09-11)

Source: `doc/01_research/ui/gpu_offload/cpu_gpu_boundary_census_2026-09-11.md`
(census rows referenced as R1..R14). Analysis by the orchestrating session;
fixes delegated. All fixes pure Simple; any new `rt_*` needs a runtime-boundary
record in `.spipe/simple_2d_web_renderer_gpu_optimization/state.md`.

## Root-cause groups

| group | rows | mechanism | fix |
|---|---|---|---|
| F1 route sampler | R2 R3 (R13) | `_web_draw_ir_key` keys on `composition.generation`; steady branch compares 8.3M px vs CPU oracle every frame; software oracle runs on a proven device when margin test fails | key on device+surface+page identity; validate on token change only via device checksum; proven device never runs the oracle route in steady state; park engine (no shutdown per frame) |
| F2 batching | R4 R5 R6 R8 R9 | fixed 256 descriptor table + `draw_text_bg` whole-batch fence flush; descriptor set per primitive; atlas CPU-rasterized per `draw_text`; clip disables font compute lane | growable/pooled descriptors; text-bg band folded into batch order without fence; atlas build behind generation cache; clip rect as push-constant in glyph compute shader (SPIR-V emitted in Simple) |
| F3 entries | R1 R14 + fallbacks | `cpu_simd` hardcoded; only `SIMPLE_GUI_BACKEND` read; probe failure -> silent `"software"`; GUI consumer downloads 33 MB and rescans it | honor `SIMPLE_2D_BACKEND`; report fallback reason; use `Engine2DReadback.checksum` + `_present_device` |
| deferred | R7 R10 R11 R12 | no GPU ellipse/bezier pipeline; masked gradient/image CPU paths; 1px stripe heuristic | separate slice; todo rows |

## Evidence bar per fix
Before/after in ONE tree with ONE binary; a spec with an absolute oracle
(known pixel value or `gpu_frame_complete` flag), not parity alone; sabotage
arm that bites. Vulkan execution on this Mac is gated on the Sep-7
`bin/release/aarch64-apple-darwin-macho/simple` being runnable — otherwise
CPU-path oracles plus dispatch/flush counters are the evidence.
