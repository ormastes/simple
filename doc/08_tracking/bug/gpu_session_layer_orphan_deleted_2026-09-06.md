# `src/lib/gc_async_mut/gpu/session/` was deleted as an orphan layer — do not restore it

Date: 2026-09-06
Status: DECISION — PENDING the delete PR's actual diff (see the last section)
Area: lib / gc_async_mut / gpu / session

Census taken at `origin/main` `461e48379ff` (2026-09-06). **This record is
written ahead of the deletion, not after it** — at the time of writing no delete
branch existed (`git ls-remote`). It states the reasoning, which is settled; the
mechanics below are the plan, not an observation. Reconcile against the delete
PR's real diff when it lands.

## What is to be deleted

All 20 files of `src/lib/gc_async_mut/gpu/session/`:

`arch_capabilities`, `backend_adapter_shared`, `backend_cpu_adapter`,
`backend_cuda_adapter`, `backend_metal_adapter`, `backend_runtime_ops`,
`backend_vulkan_adapter`, `backend_webgpu_adapter`, `graphics_capabilities`,
`graphics_error`, `graphics_session`, `graphics_session_policy`,
`legacy_wrappers`, `optimization_provider`, `optimization_registry`,
`session_api`, `session_frame`, `session_perf`, `session_types`,
`web_gui_wm_session`.

Plus its dependent unit specs (both `test/01_unit/` and the `test/unit/` mirror
tree) and the four baseline rows named below.

## Why — four independent reasons

**1. Zero product importers.** Measured at `461e48379ff`:

```
grep -rn 'std\.gpu\.session\.' src --include='*.spl' | grep -v 'src/lib/gc_async_mut/gpu/session/'
→ 0
```

Every importer was a test. Seven of the 20 modules had no importer at all, not
even a spec (`backend_adapter_shared`, `backend_runtime_ops`, `legacy_wrappers`,
`optimization_provider`, `optimization_registry`, `session_perf`,
`web_gui_wm_session`). Repo rule: *NEVER add unused code — delete completely*
(`.claude/rules/code-style.md`).

**2. Fifteen externs with no runtime definition anywhere.**
`session/backend_runtime_ops.spl:3-20` declares `rt_gpu_session_metal_{create_device,submit,present,cleanup}`,
`rt_cuda_{device_init,submit,cleanup}`, `rt_vk_{create_device,submit,present,cleanup}`,
`rt_webgpu_{create_device,submit,present,cleanup}`. An unbacked extern returns
silent nil (`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`),
so `BackendVulkanAdapter.init_device()` (`session/backend_vulkan_adapter.spl:24`)
could report success against a device that was never created.

**3. `GraphicsCapabilities.probe` is not a probe.** It queries no device: a
string -> flag table fed the caller's own declared backend/arch strings
(`session/graphics_capabilities.spl:30 static fn probe(backend, arch, bits)` at
`origin/main`). And `GraphicsSession` fabricates its device handle outright —
`session/graphics_session.spl:76`: `self.handle = self.session_id + 1000`, with
nothing behind it. (PR #410 added TODO comments above both, admitting each in
prose; those comments do **not** exist at `origin/main`, so cite the code lines,
not the comments.)

**4. The real session layer already exists, elsewhere.** The live code is
`src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl` and
`engine2d/backend_session.spl`, alongside `cpu_session`, `cuda_session`,
`metal_session`, `opencl_session`, `rocm_session`, `web_render_session`,
`web_wm_session` and `backend_vulkan_session_runtime_ops.spl` — all in
`engine2d/`, all with real importers and real dispatch. The deleted layer was a
second, consumer-less model of the same idea.

Implementing runtimes for the 15 externs would have been a multi-week,
device-required effort to give a model with no consumers a device it has no
caller for. Deletion is the correct outcome, not a compromise.

## Correction to the earlier audit: only FOUR baseline rows are removable

The audit's framing implied ~30 stale rows in
`scripts/check/unbacked_extern_baseline.txt`. That is wrong, and acting on it
would have deleted rows for live declarations and broken the ratchet.

Of the 15 externs, **only 9 have a baseline row**, and **5 of those names are
also declared elsewhere and must keep their rows**:

| name | also declared in | row keeps |
|---|---|---|
| `rt_cuda_device_init`, `rt_cuda_cleanup` | `engine2d/backend_cuda_proof.spl` | yes |
| `rt_vk_create_device`, `rt_vk_submit`, `rt_vk_present` | `engine2d/backend_vulkan_session_runtime_ops.spl` | yes |

Rows that go stale on deletion, and are the **only** four to remove:
`rt_cuda_submit`, `rt_webgpu_create_device`, `rt_webgpu_submit`,
`rt_webgpu_cleanup`. (`rt_webgpu_present` is declared in
`nogc_sync_mut/gpu/engine2d/webgpu_sffi.spl` and carries no row to begin with.)

`--generate-baseline` is not runnable on this host (it needs a deployed
`bin/simple`), so the four rows are to be removed by hand. That is the
reviewed-update path the guard documents, and it must be called out as such in
the delete commit rather than passed off as a regenerated baseline.

## Superseded work

PR #410 (OPEN as of 2026-09-06) added honest-refusal behaviour to three of these
session modules and rewrote three session specs to stop self-mocking. Those edits
were correct for a layer that had to keep existing; with the layer deleted they
have nothing left to protect and go with it. Their durable value is (a) this
record and (b) the planned move of `adapter_honesty_spec.spl` to
`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_false_success_honesty_spec.spl`,
trimmed to its engine2d-facing cases. Confirm that move actually happened before
citing it.

## Reconcile before trusting the mechanics

The four reasons above are measured at `461e48379ff` and stand on their own. The
file list, the spec move and the baseline edit are this record's *expectation* of
the delete PR. When that PR lands, diff it against this section and correct any
divergence here rather than leaving two accounts.

## If you are about to restore this directory — read first

Restoring it re-adds 15 silent-nil externs, a fake capability probe and a
fabricated device handle, with still zero product callers. If you need a GPU
session abstraction, extend `engine2d/backend_session.spl` /
`engine2d/vulkan_session.spl`; that is where the real one lives.
