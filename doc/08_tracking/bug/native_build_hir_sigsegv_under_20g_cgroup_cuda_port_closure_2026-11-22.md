# native-build worker SIGSEGVs at HIR 82/514 only under a 20 GiB cgroup (CUDA port closure)

- **Date:** 2026-11-22
- **Status:** fix-implemented-verification-pending (2026-11-26: root cause found in
  the Rust runtime's transient scope; fix + unit test implemented in 22fb17305f0 + 794d8c100d7 (unpushed), producer rebuild pending).
  The cgroup cap is not the cause; see "Root cause (2026-11-26)".
- **Severity:** P2. Blocks the end-to-end native link of the CUDA backend port
  closure, and with it the verification of `cuda_optimizer_surface_owner_2026_10_10`
  and `cuda_port_imported_method_surface_type_owner_2026_10_16`.
- **Found by:** lane `work/cuda-compiler-bugs`.

## Repro

- **Producer:** integ25 Stage 2 admitted native-build
  (`build/bootstrap-s2probe-integ25/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`
  under the integ5 pinned-src tree), sha256
  `ef46f0d2ab4274c4550530851db407bf9bad7f21bfabd50f9b56e87e77fd58d6`.
- **Runtime:** sibling `stage2-runtime-authority`.
- **Host:** Linux aarch64 (NVIDIA GB10). Source base `release/1.0.0` `3c2e4556b6d`
  plus the owner-import removal.

```
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_GO_TO_END=1 SIMPLE_FILE_WORKERS=0 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 \
  systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 <stage2> native-build \
  --source src/compiler --source src/app --source src/lib --source src/plugins/backend_cuda \
  --source src/compositions/kernel_llvm_cranelift --source test/native/cuda_compiler_bugs/port_owner \
  --entry-closure --entry test/native/cuda_compiler_bugs/port_owner/main.spl \
  --runtime-path <stage2-runtime-authority> --cache-dir <fresh> --output <out>
```

## Observed

| cgroup / config | result | peak RSS (`/usr/bin/time -v`) |
|---|---|---|
| 20G, default threads (HIR worker pool sized to 1) | `native-build worker terminated with signal 11 (SIGSEGV)`, worker exit -139, build rc 117, at HIR 82/514 | 4.01 GB |
| 20G, `--threads 1` | same, HIR 82/514 | 4.01 GB |
| 20G, `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=8388608` (HIR in-process, `[shard] threads=0`) | same, HIR 82/514 | 4.01 GB |
| 8G, unchanged (control, run twice) | passes HIR 82; one run completed HIR 514/514 | n/a |

- Only the cgroup `memory.max` differs between the crashing and passing runs,
  and peak RSS is far below either cap. So this is a compiler crash that depends
  on the cgroup limit, not memory pressure.
- In the 20G runs the HIR module order diverges right after
  `lib.nogc_sync_mut.io.process_ops`: the next module is
  `compiler.mir_opt.perf_facts` instead of `lib.nogc_sync_mut.sffi.runtime`, and
  the crash follows.
- **Candidate:** code that sizes or orders work from `shard_cgroup_memory_max_kb()`
  (`src/app/cli/shard_mem_clamp.spl`) or reads the cgroup limit elsewhere. Not yet
  bisected.

## Crash artifact

Crash report file:
`/var/crash/_home_yoon_dev_simple-integ5-20261116_build_bootstrap_pinned-src_pinned-c1a10190b978_build_bootstrap-s2probe-integ25_stage3_aarch64-unknown-linux-gnu_stage2-admitted_simple.1000.crash`.
It was written by the 20G runs. Get a backtrace from it before it rotates.

## Root cause (2026-11-26, lane work/bug-cuda-segv-20261126)

Host aarch64 GB10. Producer unchanged (`ef46f0d2…`, Rust runtime linked in).
Source tree `847afe06a41` (the 2026-11-22 base plus the owner-import removal).

### The cap only selects the parse-shard count

| run | parse shards | frontend cache | result |
|---|---|---|---|
| 20G, default | 3 (`[shard] threads=3`) | warmed by shards, `hits=384` | HIR 82/514 `process_ops`: rc 1, "frontend registry promotion failed during retained HIR lowering" (same module, checked-failure form) |
| 20G, `SIMPLE_PARSE_SHARDING=0` | 0 | `hits=0` | HIR 514/514, MIR passed, reached native_compile |
| **8G**, frontend cache copied from the 20G run, `SIMPLE_HIR_CACHE=0` | 0 | `hits=514` | **SIGSEGV at HIR 82/514 (`process_ops`), worker -139, rc 117** |

At 20G the cap admits 3 parse shards. They fill the frontend parse cache, so the
HIR coordinator lowers modules from cache hits, and that changes the allocation
pattern. Under 8G there is one parse thread, so there are no shards and no warm
cache. Reproduce at any cap: copy a warm `default/frontend` into a fresh
`--cache-dir`, then set `SIMPLE_HIR_CACHE=0`.

### Backtrace (core from 2026-11-22 09:20, and again from the 8G repro 2026-11-26 17:18)

```
#0 compiler.frontend.join_point_attr_registry.join_point_attr_promote_transient_owner  (ldr x0,[x9,x6,lsl #3], x9=0x1)
#1 compiler.frontend.retained_parse_owners_v1.frontend_promote_parse_registry_owners_v1
#2 compiler.driver.driver_source_parse_support.driver_promote_frontend_registry_owners
#3 CompilerDriver.lower_retained_surface_module
#4 CompilerDriver.lower_and_check_retained_owner_impl
```

The loop is `for dirty_fn in join_point_attr_dirty_fn_names`. The global
(`.bss` 0x26bc5f9) points at a header whose memory now holds unrelated words:
`len` = 0x73e51231 and data pointer = 1.

### Who freed the header (gdb hardware watchpoints, ASLR on, 8G recipe)

`join_point_attr_promote_transient_owner` is the writer of the global. Its
`_join_point_attr_clear_dirty()` allocates a fresh `[]` while the per-module
scope is *paused*, so the header is meant to be persistent. 68 such headers
survived. The header from module 81 (`compiler.mir.intrinsics`) did not: that
module's own scope end freed it.

```
HDRW addr=0xeaadf540
#0 _int_free (p=0xeaadf530)
#2 simple_runtime::value::collections::free_transient_objects
#3 rt_transient_array_scope_end
#5 driver_end_transient_parse_scope
#6 driver_publish_reverse_reference_parse_scope_v1
#7 CompilerDriver.lower_retained_surface_module
```

`track_transient_heap` never records paused allocations. So the scope's object
list held a **stale entry**: some object tracked earlier in that scope was freed
mid-scope, and the allocator then gave its address to the paused-born header.
`free_transient_objects` frees by registry membership of the address, so it
freed the live persistent header. Module 82 then crashed iterating it.

Only `rt_array_free` removed a freed object from the scope/session lists
(`transient_untrack_freed`). Every other single-object free went through
`unregister_heap_ptr` / `unregister_heap_ptr_checked` without untracking:
`rt_string_free`, `rt_array_free_deep`, tuple/dict/object frees, and about 20
call sites.

Which free path supplies the address: a second gdb run logged every
`unregister_heap_ptr*` entry, with its caller, after the 55th header write.
Out of 123 paused-born headers, 12 landed on an address that had just been
freed. 10 of those frees came from `rt_string_free`, the untracked path; 2 came
from `rt_array_free`, which already untracks. That run was slowed by the
logging and did not crash, so it shows the reuse pattern, not the crashing
instance itself.

The C runtime lane does not have this hole. In `core_reclaim_tracked_object_locked`,
scope end compares each array, dict, enum, closure or boxed scalar against its own
`transient_scope_id`. Strings use flags instead: a string born while the scope is
paused carries either no flag (no live session) or `TRANSIENT|SESSION`, and
scope-end reclaim skips both.

### Fix

`src/compiler_rust/runtime/src/value/heap.rs` now calls the untrack hook from
both single-object registry erases. The hook is
`collections::transient_untrack_freed_addr`, the same address-keyed tombstoning
that `rt_array_free` already did. Scope-end and session-end batch frees use
`unregister_heap_ptrs_batch` with the slot already taken, so they are unaffected.

Rust unit test
`value::collections::transient_scope_stale_entry_tests::freed_string_address_reused_while_paused_survives_scope_end`:
red on base ("persistent string freed by scope end"), green with the fix.

### Verification pending

The crashing producer embeds the old runtime. This closes when a Stage 2
producer built with the fix runs the 8G warm-cache recipe above past HIR 82/514.

### Residual holes (not closed by this fix; tracked as `transient_scope_untrack_skipped_cross_thread_or_borrowed_2026-11-26`)

The untrack still does not run in three cases:

- a free on another thread, since the scope is thread-local;
- a free while this thread's scope slot is borrowed, because `try_borrow_mut` declines;
- raw `dealloc` that bypasses `unregister_heap_ptr*`.

Any of these can still leave a stale entry. Once an address is duplicated, the
scope index is marked ambiguous for the rest of that scope, and every untrack
in that scope becomes an O(n) scan. Before this fix only `rt_array_free` paid
that scan; now every free type does. The main source of duplicates (frees that
did not untrack) is gone, but the fallback cost is still there.
