# Stage 3 self-build: `panic: text concat: registration failed` (C-only 2^24 transient-scope cap) (2026-11-20)

Bug id: `stage3_transient_scope_object_cap_panic_2026-11-20`
Status: fixed in `src/runtime/runtime_native.c`. It takes effect when the next
Phase 3 links Stage 3 from this source.

## Symptom

`stage3-i22.simple` ran the Stage 3 → Stage 3 `native-build` with
`SIMPLE_MIR_SHARD_COUNT=14`, and again with 28. The first MIR shard worker dies
with exit 1 in both runs:

```
panic: text concat: registration failed
[mir-shard] owner=0/14@0 status=BLOCKED exit=1 claimed=8 sealed=8 finished=false
[mir-shard] owner=0/14@0 ICE[mir_lower] module compiler.frontend.generated.ast_semantic_value (attributed) ...
```

- The failure reproduced on two source trees: integ18 `cbff0ece9e84` and integ22
  `e1b8cc35359`.
- Changing the shard count from 14 to 28 changed nothing.
- The Stage 2 binary runs the same Phase 3 work with no failure.

## Root cause

**1. The panic site.**
- `rt_core_concat_bytes_v1` panics when `rt_core_register_string` returns 0.
- That happens when `rt_core_track_transient_immortal` refuses to grow the
  tracking list of the live transient scope.
- The list refused growth past `RT_CORE_TRANSIENT_SCOPE_MAX_OBJECTS = 1 << 24`
  entries. The constant was introduced in `a04600b188e` with no stated reason.
- The list only shrinks at scope end. So this capped the number of
  **allocations made inside one scope**, not the number of live objects.

**2. Why only Stage 3.**
- The Stage 2 binary links the **Rust** runtime. Its
  `TransientHeapScope.objects` is a plain `Vec`:
  `src/compiler_rust/runtime/src/value/collections.rs`, `track_transient_object`
  (`scope.objects.push(value)`). It has no count limit.
- Stage 3 is the first stage that links the **core-C** runtime
  (`--runtime-bundle core-c-bootstrap`; `runtime_native.c` is compiled into
  `simple_rt_<pid>_..._runtime_native.o` at link).
- So the same pass that passes on Stage 2 panics on Stage 3. This is a C/Rust
  twin divergence.

**3. Where in the worker.**
- The ICE names the module that last closed a `mir_lower` breadcrumb. That
  attribution is wrong.
- `NATIVE_STAGED_CODEGEN_DEFAULT_BATCH_V1 = 8`
  (`80.driver/driver_build/native_staged_codegen.spl:37`), and the worker had
  `claimed=8`.
- After the 8th lowered module, the loop runs `native_staged_codegen_flush_v1`
  (`driver_pipeline_lowering.spl`, flush after `staged_pending` reaches the batch
  size). The panic is in that first batch flush.
- The flush runs these passes over the 8 largest modules:
  - verify;
  - borrow check;
  - opt, which returns early at `opt_level` 0;
  - codegen.
- Its per-module transient scopes are:
  - `borrow_check_module_scoped_v1` (`driver_pipeline_passes.spl:63`);
  - the backend scope in `compile_module_with_backend_scoped_v1`
    (`70.backend/backend/backend_helpers.spl:414`).

**4. Measured with gdb.**
- Run: the same `stage3-i22.simple` on a 77-module fixture closure (entry imports
  `compiler.frontend.generated.ast_semantic_value`), with `--backend cranelift`.
- Method: gdb follows the shard worker, with breakpoints on
  `lib.nogc_sync_mut.sffi.transient.transient_scope_pause`,
  `compiler.mir._MirLowering.transient_owner_sffi.transient_array_scope_pause_v1`
  and `spl_cranelift_new_aot_module_config_v2`. It reads the TLS
  `rt_core_transient_heap_scope_object_len` at each pause.
- Results, as the largest single-scope count per pass:

  | per-module scope | largest count in the 77-module closure |
  |---|---|
  | borrow check (`borrow_check_module_scoped_v1`) | **2,061,022** |
  | MIR lowering (`lower_module_transient_scoped`) | 3,170,897 |
  | cranelift backend scope at `cranelift_new_aot` (storage lowering + backend MIR copy) | 3,317 |

- The real failing batch holds:
  - `switch_operators_calls` (660 KB);
  - `expr_dispatch` (605 KB);
  - `method_calls_literals` (515 KB);
  - `hir_codec` (446 KB);
  - and 4 more modules of 256–350 KB.
- **Extrapolation, not measured:** one borrow-check scope over the largest of
  these modules exceeds 2^24 allocations. The measured count reaches 2.06M on a
  closure whose largest module is 256 KB.
- The backend scope is about 3K entries before Cranelift, so it is not the
  candidate.

## Hypotheses checked and refuted

**"A scope is never exited, so objects accumulate across modules."** Refuted:
- `rt_transient_array_scope_begin` refuses while the list is non-empty
  (`runtime_native.c`, `rt_core_transient_heap_scope_object_len != 0`). A
  leftover scope would therefore turn every later per-module scope into a loud
  `[mir-scope]` / `[borrow-scope]` / `[codegen-scope] WARNING transient scope
  refused` line.
- Both failing logs contain zero such lines.
- In the fixture, every per-module scope pause shows a fresh count.

**"Smaller shards keep each worker under the cap."** Refuted: the 28-shard rerun
(`w-s3s3i22b`) failed identically, with `claims=8 sealed=8` on the same module.
The limit is per scope, and worker 0 always gets the same first batch of 8.

## Fix

`src/runtime/runtime_native.c`, `rt_core_track_transient_immortal`:
- The count limit is removed. Growth is bounded only by `SIZE_MAX` and the
  allocator, which is twin parity.
- `RT_CORE_TRANSIENT_SCOPE_WARN_OBJECTS` (default 2^24, `#ifndef`-overridable)
  is now advisory. The first time a scope crosses it, the runtime prints one
  stderr line per scope:
  `[transient-scope] WARNING scope <id> tracks more than <n> objects; continuing`.
  A pathological scope stays visible without being fatal.

This removes a C-only divergence. **It is not a leak fix, because no leak was
found.** The objects in the list are the per-module pass arena. They are already
allocated, and scope end frees them. The list itself costs 12 bytes per entry.

Not done:
- **Degrade to unscoped/immortal on overflow.** This was rejected as unsafe.
  Promotion stops at persistent nodes, so an immortal object made after the
  limit could point at transient children that scope end frees.
- **Diverting overflow to the session list.** This has the same hazard.

## Evidence

The selfcheck is `src/runtime/test/rt_transient_scope_object_cap_selfcheck.c`.
It includes `runtime_native.c` with a lowered advisory threshold and covers:
- the exact defect: `rt_string_concat` registrations past the threshold in one
  scope;
- a generalization spec: arrays plus boxed floats past the threshold;
- that scope end reclaims everything;
- that the warning fires once per scope;
- that an under-threshold scope stays silent.

| build | result |
|---|---|
| pre-fix runtime, `-DRT_SCOPE_CAP_CHECK_COUNT=16777280` (2^24+64) | **exit 101** (`spl_panic`), 3.5 s, RSS 0.98 GB |
| fixed runtime, same count, production threshold | **PASS**, 13.1 s, RSS 1.25 GB, one warning |
| pre-fix runtime, default small count | FAIL (no warning; line 109) |
| fixed runtime, default small count | PASS (12856 checks) |

Build line (also in the file header):
`clang -std=c11 -D_GNU_SOURCE -pthread -O1 -ffunction-sections -fdata-sections -Wl,--gc-sections -fuse-ld=lld -o /tmp/cap src/runtime/test/rt_transient_scope_object_cap_selfcheck.c -lm -ldl`.

Below the threshold, the code adds only one compare and branch per tracked
object.

## Next blocker (separate, already recorded)

`stage3-i22.simple` is a core-c-bootstrap producer, so `spl_cranelift_new_aot_module_config_v2`
is a NAMED TRAP in it. In the fixture, the worker SIGABRTs at the first
`cranelift_new_aot`.

So a Stage 3 → Stage 3 self-build with `--backend cranelift` aborts in the first
codegen even with this fix. It must use `--backend llvm`. See
`cranelift_core_c_bootstrap_trap_misattributed_as_module_ice_2026-10-19.md`.

The borrow-check scope is backend-independent, so this fix is still required on
the llvm lane.

## Rebuild needed

The core-C runtime is compiled from source at Phase 3 link time, and the Stage 2
binary runs on the Rust runtime. So the Stage 2 binary does not need to be
rebuilt. Rerunning Phase 3 from a tree that contains this change links a Stage 3
that carries the fix.
