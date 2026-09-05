<!-- codex-research -->
# Local research: container/GPU 8K80 completion

## Scope

This research separates two non-physical completion lanes from physical 8K80
presentation: (1) the A4 native DrawIR retained-damage carrier and (2) the A5
strict semantic producer plus the software portion of A7 aggregation.

## Findings

- `test/05_perf/graphics_2d/draw_ir_damage_8k_bench.spl` is intentionally CPU:
  it requests `DRAW_IR_BACKEND_CPU`, creates Engine2D with `cpu`, and rejects a
  different selected backend. It can run headlessly in a container, but CUDA
  presence cannot turn this receipt into GPU evidence.
- The benchmark already emits the exact 7680x4320 viewport, 20 revisions,
  256x128 damage rectangle, command counts, p50/p95, final readback, checksum,
  mismatch count, and an outer-harness RSS marker. The older bug's `7680x43`
  description is stale; source truth is 256x128.
- `tools/gui_perf_bench/run_all_benchmarks.shs` builds the semantic exporter but
  invokes only `cpu_simd` and `software`. Its CUDA row is a direct buffer-fill
  measurement, not Web/GUI/WM -> DrawIR -> Engine2D evidence.
- The Web renderer owns a semantic Engine2D path, but unavailable Vulkan can
  resolve to software. A strict producer must emit requested and selected
  backend, readback source, handle/device identity, fallback, completion,
  checksum, revision, and timing, and must reject silent software resolution.
- The existing container suite has no `--gpus` admission and its image is not
  CUDA/Vulkan-ready. A new bounded wrapper must verify actual CUDA submission
  and Vulkan device visibility rather than trusting `nvidia-smi` inventory.
- No admitted native DrawIR carrier exists. TODO666, TODO667, TODO682, TODO686,
  and TODO687 form the current Stage 4/native-build prerequisite chain.
- A6/A8 remain physical-only through TODO684/TODO685. A headless aggregate may
  report the software lanes passing, but must remain `blocked-physical` until a
  correlated physical receipt is supplied.

## Parallel research record

- Compiler/native lane: audited the Stage 4/native-build chain and A4 receipt.
- GPU/container lane: audited Docker, CUDA, Vulkan, and semantic-render routes.
- Acceptance/Todo lane: audited A1-A8 scope, contradictions, and remaining rows.
- Merge owner: root Codex; final review: independent highest-capability agent.
