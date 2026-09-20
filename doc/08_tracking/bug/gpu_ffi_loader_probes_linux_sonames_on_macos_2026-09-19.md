# GPU FFI loader probes Linux sonames on macOS (and `spl_dlopen` raises where `DynLib.load` expects nil)

- Status: FIXED (2026-09-20) in pure-Simple `src/lib` — both acceptance specs PASS on the macOS host (CUDA: clean nil; Vulkan: real loader via homebrew dylib)
- Fixed: 2026-09-20
- Found: 2026-09-19
- Component: `src/lib/nogc_sync_mut/gpu/engine2d/ffi_dispatch.spl` (`gpu_lib_candidates`, :60-84), `src/lib/nogc_sync_mut/sffi/dynamic.spl` (:121-128), seed runtime `spl_dlopen`
- Binary: deployed Rust seed (macOS aarch64)

## Observation

`gpu_lib_candidates()` selects `.dylib` candidate names only when the env var `SIMPLE_OS_TYPE == "Darwin"`, but **nothing in the repo ever sets `SIMPLE_OS_TYPE`** (grep over src/scripts/bin finds zero setters; it is unset in the environment). Result: even on this macOS host the loader probes Linux sonames (`libvulkan.so.1`, `libcuda.so.1`), finds nothing, and:

- per the documented comment at `dynamic.spl:121-128`, the interpreter lane's raw `spl_dlopen` **raises and aborts** on an unresolvable bare soname instead of returning a handle — so `DynLib.load`'s nil path is unreachable and the in-spec `if ffi == nil` guard never gets control;
- Simple has no try/catch (`src/lib/nogc_sync_mut/spec.spl:17`), so no spec-side guard is possible.

Concrete impact (2026-09-19, macOS host with Vulkan installed at `/opt/homebrew/lib/libvulkan.dylib`):
- `test/01_unit/lib/gpu/engine2d/ffi_cuda_spec.spl` "loads the installed CUDA driver": `runtime: spl_dlopen failed for 'libcuda.so.1'` (host has no CUDA — expected unavailable, but should be a clean nil, not a raise);
- `test/01_unit/lib/gpu/engine2d/ffi_vulkan_spec.spl` ledger/`is_available`: `runtime: spl_dlopen failed for 'libvulkan.so.1'` — the run never tries the installed `.dylib` names.

## Fix direction

1. Platform detection at the source: derive the Darwin branch from an env that IS set (e.g. `rt_platform_os()` / uname-based runtime query) or set `SIMPLE_OS_TYPE` in the CLI/runtime entry; do not depend on an unset env var.
2. Seed-side (record-only; seed is bootstrap-only per project rules): `spl_dlopen` should return nil/raise only at the `DynLib.load` boundary so the documented nil path is reachable — or the .spl layer should probe with a non-raising variant first.
3. Re-run the two specs above; a clean `ffi == nil` on a no-device host is the acceptance signal (and `ffi != nil` using the homebrew Vulkan on this host).

## Related

- `gated_specs_are_tautology_shells_2026-08-09` (the lane that surfaced this; its 2 remaining reds are this defect)

## Resolution (2026-09-20)

All fixes are pure-Simple, in `src/lib` only; the Rust seed was not touched.

1. **Platform detection (defect 1).** `gpu_lib_path`/`gpu_lib_candidates` in all
   four GPU dispatch owners (`gpu/engine2d/{ffi,sffi}_dispatch.spl`,
   `gpu/engine3d/{ffi,sffi}_dispatch3d.spl`) no longer read the never-set
   `SIMPLE_OS_TYPE`. They now call `std.nogc_sync_mut.env.platform.detect_os()`,
   which consults the in-process `rt_platform_name()` primitive first and falls
   back to env/`uname -s` — the canonical repo idiom (same import already used
   by `gpu_provider_probes.spl`). The macOS candidate list additionally probes
   `/opt/homebrew/lib/lib{name}.dylib` and `/usr/local/lib/lib{name}.dylib`,
   because dyld does not search Homebrew's lib dir for bare sonames (no
   `DYLD_*` env on this host); absent absolute candidates are rejected by the
   `file_exists` pre-probe in `std.sffi.dynamic` before any dlopen attempt.
2. **Non-raising nil path (defect 2).** `_sffi_dlopen_checked` and
   `_sffi_dlsym_checked` (`src/lib/nogc_sync_mut/sffi/dynamic.spl`) previously
   fell back to the raw `spl_dlopen`/`spl_dlsym` ABIs on ANY checked-ABI
   failure; in the interpreter lane those raw ABIs raise and abort
   (`spl_dlopen failed for '<path>'`). They now return `Err` immediately when
   the checked ABI reports a non-zero status (genuine failure), so
   `DynLib.load` reaches its documented nil path. The raw-ABI fallback is kept
   ONLY for the `status == 0 && out == 0` shape, which is the out-param
   writeback-loss signature of a pre-2026-09-11 seed interpreter lane — there
   the load already succeeded, so the retry cannot raise. Callers that
   document raising behavior (`DynLib.open`, `DynLoader.call*`) are unchanged.
3. **Newly unmasked defect fixed: `VulkanDynFfi` ledger dropped on the
   interpreter lane.** With the loader fixed, `ffi_vulkan_spec.spl` reached its
   DEVICE-RAN branch for the first time and exposed that the tree-walk
   interpreter (the lane `bin/simple test` uses) drops ALL class-field mutations
   performed through an option-typed receiver: `create_dynamic()` returns
   `VulkanDynFfi?`, so `ffi.init()` mutated a temporary receiver copy and
   `rejected_op_count()`/`last_rejection()` never observed it (characterized
   with probe classes in `build/`; related family:
   `jit_class_mutation_drop_characterization_2026-07-04.md`). Fix: the ledger
   is boxed behind per-instance `AtomicI64` handles
   (`std.nogc_sync_mut.atomic`), which mutate runtime-owned storage and
   survive receiver copies; `last_rejection` round-trips through a fixed
   op-code table (`_reject_op_code`/`_reject_op_name`). Plain fields remain in
   place for lanes with class-reference semantics would be wrong here — the
   handle box is the repo-sanctioned pattern for mutation-dropping lanes.
4. **Seed-side note (record-only, per project rules the seed is
   bootstrap-only):** the interpreter's raw `spl_dlopen`/`spl_dlsym` still
   raise on failure; the checked variants (`spl_dlopen_checked` status 2,
   `spl_dlsym_checked` status 3) are non-raising and are now the only ABIs the
   .spl layer uses on failure paths.

## Verification (2026-09-20, macOS arm64, deployed seed binary)

- `bin/simple test test/01_unit/lib/gpu/engine2d/ffi_cuda_spec.spl` — **PASS**
  (clean `ffi == nil`, `SKIPPED: libcuda not loadable`, no runtime raise; host
  has no CUDA).
- `bin/simple test test/01_unit/lib/gpu/engine2d/ffi_vulkan_spec.spl` — **PASS**
  (real dlopen of `/opt/homebrew/lib/libvulkan.dylib`; all four `it`s run their
  DEVICE-RAN branches, rejection ledger asserts 0→1→2 with names init/shutdown).
- Regression: `ffi_dispatch_spec.spl`, `ffi_vulkan_dynamic_honest_gate_spec.spl`,
  `ffi_cuda_out_param_marshalling_spec.spl`, `wffi_into_bytes_spec.spl`,
  `dynamic_versioned_spec.spl` — all PASS.
- Pre-existing, unrelated: `test/01_unit/sffi/sffi_public_api_spec.spl` fails 5
  `cli_*` cases (`cli_get_args` nil-check, `cli_dispatch_rust`, `cli_lint`,
  `cli_fmt`) — those call `rt_cli_*` externs directly with no path to
  `DynLib`; fails identically without this change (interpreter-lane
  limitations, same class as "rt_cli_run_lint is not supported in interpreter
  mode").
- `test/02_integration/rendering/macos_vulkan_provider_micro_probe.spl` is an
  args-driven diagnostic script, not a describe/it spec (`test` runner reports
  zero examples by design).
