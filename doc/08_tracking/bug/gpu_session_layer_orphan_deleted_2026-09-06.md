# The `gpu/session/` layer was an orphan and was deleted (2026-09-06)

**Status:** RESOLVED by deletion. **Scope:** `src/lib/gc_async_mut/gpu/session/` (20 files),
its 6 dependent unit specs across both test trees, and one trimmed/moved spec.

## What was wrong

`src/lib/gc_async_mut/gpu/session/` modelled a GPU "graphics session" with five backend
adapters (metal/webgpu/vulkan/cuda/cpu), a capability probe, an optimization registry and a
frame contract. **Nothing in `src/` ever imported it.** Its adapters declared 15 `rt_*`
externs in `backend_runtime_ops.spl` that have no runtime definition anywhere in the tree,
so every device path it modelled returned nil or a fabricated handle. The live session
surface the product actually uses is `src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl`
plus `src/lib/gc_async_mut/gpu/engine2d/backend_session.spl` (`backend_session_create` /
`_retain` / `_release`), reached from `engine2d_api.spl`, `render_2d_x86_session.spl` and
`render_2d_riscv.spl`.

PR #410 rewrote three of the layer's specs to make the layer stop reporting false success.
That work is superseded here: with the layer deleted there is nothing left to lie. The
repo rule is explicit — "NEVER add unused code", "delete completely".

## Census that justified the deletion (at PR #410's head `a5990b23ed2`)

Per module (20 of them), `grep -rln 'gpu\.session\.<module>' src test scripts config doc/06_spec`
excluding the directory itself:

- **`src/` importers outside the directory: 0** — for every one of the 20 modules.
- Test importers: exactly 5 specs (the 3 PR #410 rewrote, `adapter_honesty_spec`,
  `session_frame_contract_spec`).
- 7 modules had **no importer at all**, not even a spec: `backend_adapter_shared`,
  `backend_runtime_ops`, `legacy_wrappers`, `optimization_provider`, `optimization_registry`,
  `session_perf`, `web_gui_wm_session`.
- Symbol-level cross-check: all 70 top-level `class`/`fn`/`enum` names in the layer were
  word-grepped across `src` and `test`. Every `src/` hit was an unrelated namesake
  (`AdapterCapabilities` in the DAP tree, `next_session_id` in the debugger, the engine2d
  `backend_session_*` functions) or a prose comment (`game2d_session.spl:3`,
  `game3d_session.spl:3` say "Wraps GraphicsSession lifecycle" but import only `std.io`).
- No `FILE.md`, `mod.spl`, `__init__.spl` or `src/lib/simple.sdn` entry named `session`.

## What was deleted / moved

Deleted (`git rm`):

- `src/lib/gc_async_mut/gpu/session/` — all 20 `.spl` files.
- `test/01_unit/gpu/{graphics_session,session_mode_separation,backend_session_sharing}_spec.spl`
  and their pre-rewrite mirrors under `test/unit/gpu/` (both trees; removing an unbaselined
  pair is neutral for `check-test-tree-divergence`).
- `test/01_unit/lib/gc_async_mut/gpu/session/session_frame_contract_spec.spl`.

Moved and trimmed:

- `test/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.spl` →
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_false_success_honesty_spec.spl`.
  Dropped the 5 adapter imports, the 5 adapter `@cover` lines, the two
  `*_still_ends_in_bare_success_sentinel` source-scan helpers (their only callers were the
  dropped cases), the now-unused `shell_output` import, and the contexts "sites 15-19",
  "vulkan adapter init_device/submit/present" and "site 20". Kept every case that guards
  live product code: site 11 (`WebGpuBackend.init`), sites 13/14 (Vulkan ICD), the DXVK
  d3d11 probe, and the `engine.spl` mitigation unification. 18/18 before the trim → **7/7
  after**, both green under the seed.

## Baseline / gate rows that go stale (owned by the parallel baseline lane, not this commit)

- `scripts/check/unbacked_extern_baseline.txt`: `rt_cuda_submit`, `rt_webgpu_create_device`,
  `rt_webgpu_submit`, `rt_webgpu_cleanup` become stale. The other 5 of the 9 rows
  (`rt_cuda_device_init`, `rt_cuda_cleanup`, `rt_vk_create_device`, `rt_vk_submit`,
  `rt_vk_present`) must stay — those names are also declared in
  `engine2d/backend_cuda_proof.spl` and `engine2d/backend_vulkan_session_runtime_ops.spl`.
- `scripts/check/use_target_resolves_baseline.txt`: every row whose file column is under
  `src/lib/gc_async_mut/gpu/session/`, plus rows for the deleted/moved specs.
- `scripts/check/directory_fanout_baseline.txt:438` (`src/lib/gc_async_mut/gpu/session\t20`).
- `scripts/check/spec_vacuity_semantic_baseline.txt:316`
  (`SHADOW test/unit/gpu/session_mode_separation_spec.spl`).
- **`scripts/check/raw_sffi_unsafe_baseline.tsv:2853-2867` — 15 rows keyed on
  `src/lib/gc_async_mut/gpu/session/backend_runtime_ops.spl`.** Found during this deletion
  and NOT listed in the original plan; it is the largest stale-row group and must be removed
  with the rest.
- `test/03_system/gui/wm_host_platform/wm_false_success_family_spec.spl:44,122` — predicate 2
  shell-globs `session/backend_*_adapter.spl` and would now scan nothing (a vacuous PASS).
- `test/fixture/interpreter_extern/vk_capability_gap_probe.spl:3` — comment points at the
  deleted `backend_runtime_ops.spl`.
- `scripts/audit/metal-sffi-symbol-identity.shs:6,39` — asserts the deleted file declares
  exactly 4 `rt_gpu_session_metal_*` externs; a check against a missing file.

## Known dangling references intentionally left alone

- `doc/06_spec/01_unit/gpu/{backend_session_sharing,graphics_session}_spec.md`,
  `doc/06_spec/unit/gpu/graphics_session_spec.md` and
  `doc/06_spec/01_unit/lib/gc_async_mut/gpu/session/adapter_honesty_spec.md` are generated
  sspec mirrors of deleted/moved specs. `doc/06_spec` is generated and marked DO-NOT-REFACTOR
  in `.claude/rules/structure.md`; they are recorded here rather than hand-edited, and will be
  regenerated (or pruned) by the sspec docgen lane.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl:494` mentions the old
  `session/adapter_honesty_spec.spl` path in prose; that file is owned by a parallel lane this
  session and was not touched.

## Verification actually run

Seed: `src/compiler_rust/target/bootstrap/simple` (banner: "this Rust-built Simple binary is a
bootstrap seed only"). `bin/simple lint` SIGSEGVs on this host and was NOT run — no lint claim
is made. No bootstrap of any kind was performed.

| spec | before | after |
|---|---|---|
| `adapter_honesty_spec.spl` (pre-trim) | 18/18 OK rc=0 | — |
| `backend_false_success_honesty_spec.spl` (post-trim) | — | 7/7 OK rc=0 |
