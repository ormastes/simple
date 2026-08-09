# GPU Debugger Common Interface — Parallel Implementation Plan

**Design:** `doc/05_design/app/tools/gpu_debugger_common_interface_architecture_2026-08-09.md`
(read in FULL before starting any stream — §ref numbers below point there)
**Status:** PLAN ONLY — approved for planning 2026-08-09; agents not yet launched.
**Related plans (check overlap before touching shared files):**
`metal_gpu_lane_and_vulkan_jit_notebook_parallel_plan_2026-08-09.md` (streams
N1-N9, some in flight — D4-metal below depends on its N2/N3 landing).

**Ground rules for every agent** (identical to the Metal plan's — repeated
here so each agent needs only this doc + the design doc):
- Never work directly in `/home/ormastes/dev/pub/simple` (shared, contested;
  origin/main moves multiple commits/minute).
  `cd /home/ormastes/dev/pub/simple && git fetch origin main`, then
  `git worktree add /home/ormastes/dev/pub/simple-<stream>-wt origin/main --detach`;
  work there; `git worktree remove ... --force` when done.
- Commit in your worktree, push directly:
  `timeout 90 env GIT_SSH_COMMAND="ssh -o BatchMode=yes -o ConnectTimeout=10 -i ~/.ssh/id_ed25519_this_mac" git push git@github.com:ormastes/simple.git HEAD:refs/heads/main`.
  On non-fast-forward: fetch, verify `git diff --quiet <old> <new> -- <your files>`
  is silent, rebase, retry. Real overlap → STOP and report.
- `SIMPLE_MODULE_LIMIT=4000` on every `bin/simple test`.
- Never weaken an assertion; RED + bug doc beats fake green.
- Metal device paths skip on this Linux host by design — assert the skip is
  clean and correctly-reasoned; never "fix" a correct skip.
- Disk full ("No space left on device") → STOP and report.

## Dependency graph

```
D1 (DBG-1 + ref_vm + conformance vectors)   ── foundation, start first
 ├─ D2 (trait + ref_debug_session + unit specs)      needs D1
 │   ├─ D3 (cuda + vulkan device kernels + wrappers + env specs)  needs D1,D2
 │   │    └─ D4-metal (metal kernel DBG-1 + wrapper)  needs D3 pattern + Metal plan N2/N3 landed
 │   ├─ D5 (DAP GPU session)                          needs D2 only (ref-backed)
 │   ├─ D6 (Lab/notebook debug endpoints)             needs D2 only (ref-backed)
 │   └─ D7 (simple config + bare `gpu` tag resolver)  needs nothing from D1! see below
 └─ D8 (debug map: svmg_asm_with_map + line breakpoints)  needs D1 only loosely
D9 (docs: lane_matrix notes, Metal-pending tracking, wiki)  last
```

D7 is independent of the debugger core (it resolves mode-spec strings) and
can start immediately in parallel with D1.

## Stream D1 — DBG-1 protocol + ref_vm + debug conformance vectors

Design §3. The foundation; everything else builds on it.
- Add DBG-1 offsets/flags/sentinel to `src/lib/common/svmg/mailbox_const.spl`
  (pick the block offset from genuinely free arena space; assert no overlap
  with REG block / LOG ring / RECORD ring in a unit spec).
- Implement save/restore/breakpoint-check in `ref_vm.spl`'s `SvmgVm` — gated
  entirely on `DBG_FLAGS != 0`; zero behavior change otherwise.
- Author the debug conformance vector table (D3-style):
  `test/fixtures/svmg/debug_conformance_vectors.spl` — break-at-pc, step-N,
  resume-to-completion, break-inside-loop, resume-with-persisted-arena,
  budget-expiry-while-debugging, breakpoint-table-full.
- Unit specs: `dbg1_block_encode_spec.spl`, ref_vm debug vectors green.
- **Regression gate:** existing `test/02_integration/svmg/conformance/
  conformance_suite_spec.spl` (ref_vm suite) unchanged and green.

## Stream D2 — `GpuDebugSession` trait + ref implementation + factory

Design §4. Files: `src/lib/gc_async_mut/gpu_lane/gpu_debug_session.spl`
(trait + `GpuDebugState`), `ref_debug_session.spl` (host `SvmgVm` behind the
trait), `gpu_debug_session_for(mode_spec)` factory (jit(...) specs get the
honest skip per design §8).
- Unit spec `gpu_debug_session_ref_spec.spl`: the FULL trait contract against
  ref (this is the feature's primary behavioral spec — be thorough).

## Stream D3 — CUDA + Vulkan: kernels, wrappers, env specs

Design §3 (kernel changes) + §4 (wrappers) + §9 Tier 2.
- DBG-1 in `svmg_cuda_kernel.ptx` and `svmg_vulkan_kernel.spv` (rebuild the
  .spv from .spvasm per whatever the existing kernel build convention is —
  check the sibling `.sha256`/`.spvasm` files and any check-in script).
- `cuda_debug_session.spl`, `vulkan_debug_session.spl` — thin, delegate to
  existing lane sessions; cross-launch continuity via the persisted-arena
  mechanism (absolute-offset copy — see the 2026-08-08 bug docs; do NOT
  reintroduce the relative-offset bug).
- Env specs (live device, this host has both): run the debug vector table on
  device, diff against ref results field-for-field.
- **Regression gates:** `cuda_vm_executor_conformance_spec` 2/2,
  `vulkan_vm_executor_conformance_spec` 2/2, `cuda_exec_spec` 4/4,
  `vulkan_exec_spec` 3/3 — all with DBG_FLAGS==0, proving the kernel edits
  are inert when debugging is off. Run these YOURSELF fresh.

## Stream D4-metal — Metal wrapper + kernel DBG-1 + unit/env specs

Design §4/§9; user requirement: Metal gets full unit tests + env tests even
though device verification waits for a Mac.
- **Gate:** requires the Metal lane plan's N2 (`metal_lane_session.spl`) and
  N3 (`svmg_metal_kernel.metal`) to have landed on origin/main — check
  before starting; if N3 hasn't landed, implement the wrapper against N2 +
  design-doc kernel contract, add DBG-1 to whatever kernel state exists, and
  say so honestly in your report.
- `metal_debug_session.spl` + `metal_debug_session_unit_spec.spl` (runs on
  Linux: routing, probe skip propagation, DBG block construction, synthetic
  readback decode) + `metal_debug_session_env_spec.spl` (device vectors;
  asserts the CLEAN SKIP path on this host).
- Extend the Metal-pending tracking doc (design §9 disclosure).

## Stream D5 — DAP GPU session (IDE integration)

Design §5. New files under `src/app/dap/` (`gpu_session.spl`,
`gpu_adapter.spl`); do not restructure existing local-session files.
Unit-test the full DAP request/response mapping against `ref_debug_session`
(feed protocol JSON, assert responses — extend the existing DAP spec
pattern). Env-level: one live-CUDA DAP round-trip spec (host-aware skip).

## Stream D6 — Lab/notebook debug endpoints

Design §7. Endpoints on `lab_server.spl` (`.../debug`, `.../debug/step|resume|break`,
`GET .../debug/state`). Reuse the existing lab spec pattern
(`lab_http_api_spec.spl`'s real-subprocess/real-socket driver — and note its
hard-won lessons: portfile poll loop constants, daemon timeout behavior).
Ref-backed by default (works with no GPU); live-CUDA case where present.
Coordinate: `lab_server.spl` is a hot file for concurrent sessions — fetch
fresh, keep the diff tight, push fast.

## Stream D7 — Simple config + bare `gpu` tag (INDEPENDENT — start first)

Design §7b. `resolve_gpu_mode_spec(tag, config)` shared helper; `[gpu]`
section in the EXISTING project config (find it — do not invent a new config
file); wire into: notebook magics (`%gpu`), Lab API (`{"gpu": true}`), DAP
launch config (`"gpu": true`), and the D2 factory (when D2 lands; ship the
resolver + notebook/Lab wiring without waiting).
- Unit-test the full resolution matrix with fake probe injection: explicit
  spec passthrough / gpu+configured backend / gpu+auto probe order
  cuda→vulkan→metal / no tag = host / nothing available = honest error
  listing per-backend skip reasons.

## Stream D8 — Debug map (source→pc)

Design §6. `svmg_asm_with_map` + `SvmgDebugMap` in
`src/lib/common/svmg/debug_map.spl`; existing `svmg_asm` and its callers
untouched. Unit spec asserts line→pc pairs for a known fixture program.
Feeds D5's `setBreakpoints`(line)→pc translation — coordinate the interface
via the design doc, land independently.

## Stream D9 — Docs (last)

`lane_matrix.md` per-lane debug notes; Metal device-pending tracking doc
(with D4-metal); LLM wiki entries per the repo's pre-commit wiki rule
(`doc/00_llm_process/feature_expert/` — a new `gpu_debugger/skill.md` hub);
update this plan's Status line.

## Suggested launch order

Wave 1 (parallel): **D1, D7** (+ D8 if capacity — only loosely coupled to D1).
Wave 2: **D2** (after D1), then **D3, D5, D6** in parallel (D5/D6 only need D2).
Wave 3: **D4-metal** (after D3 pattern + Metal plan N2/N3), **D9** last.

## Definition of done

Design doc §10, verbatim — every stream's verify step actually run and
reported, never assumed. Fresh regression runs of the four existing GPU
lane/notebook spec suites are part of D3's gate, not optional.
