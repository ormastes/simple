# aarch64 freestanding: `arr[i] = v` index-set followed by `return` lowers to `call rt_index_set; udf` — trap on first cache-hit

Date: 2026-09-25
Lane: lane-C1 aarch64 guest milestone (clang bring-up), found at Wall 9
Severity: latent trap; fires the first time any affected site executes at
runtime.  Masked until now because every prior boot either never ran these
sites or took the array-push (cache-miss) path around them.

## Symptom

run-20260925_224703 (Wall 9 streaming payload loader): after the 115 MiB
/CLANG.ELF payload pumped fully into the raw region (traces 301-306 =
clusters 512..3072 of 3513, heap flat at ~37 MiB), the boot trapped during
the positioned close:

```
[arm-fs-trace] 306 0x132
FAULT @ 0x0000000040251e14
ESR=0x02000000
FAR=0x0000000040251dfc
```

addr2line: 0x40251e14 is inside
`src__lib__nogc_async_mut__fs_driver__fat32_core__Fat32Core_dot__cluster_cache_put`
(FAR is stale/irrelevant for this exception class — the crt0 handler prints
it unconditionally).

## Root cause (byte-exact)

`Fat32Core._cluster_cache_put`'s cache-hit arm
(src/lib/nogc_async_mut/fs_driver/fat32_core.spl:426) is
`self._cluster_cache_values[i] = data` immediately followed by `return`.
The freestanding compiler lowers that index-set to a call to `rt_index_set`
and then — instead of the function epilogue — emits an undefined-instruction
trap:

```
40251e04: mov  x2, x19        ; value
40251e08: mov  x1, x0         ; tagged index (rt_value_int result)
40251e0c: mov  x0, x21        ; _cluster_cache_values
40251e10: blr  x9             ; rt_index_set (0x402028a0)
40251e14: udf  #49439         ; ← ELR: trap when rt_index_set returns
```

`rt_index_set` at 0x402028a0 is a normal returning function (prologue,
IS_HEAP/type==HEAP_ARRAY checks, `lsr #3` index decode, `len` bounds check
against `[x9, #8]`, conditional store, `ret`).  It returns to 0x40251e14 and
the `udf` fires.  There is no branch around the trap; the next function
(`read_cluster`) starts at 0x40251e18.  The same function's PUSH path
(cache-miss) ends in a proper epilogue + `ret` at 0x40251d00, so `return`
per se lowers correctly — it is the index-set-then-return shape that traps.

## Blast radius: 8 identical sites in the clang-bringup kernel

All `blr`-then-`udf #49439` sites in build/os/simpleos_arm64_clang_bringup.elf
(out of 29,185 `blr`s — a specific lowering shape, not a codegen idiom):

| Site | Function |
|---|---|
| 0x40251dc8, 0x40251e10 | Fat32Core._cluster_cache_put (both index-set arms) |
| 0x40299518 | dbfs device_commit_owner._record_blob |
| 0x403242ac | ipc capability PrivilegeTable.set |
| 0x4032477c | ipc capability PrivilegeTable.add_peer |
| 0x403251d8 | ipc capability register_task_vmspace |
| 0x4034c6e8 | ipc syscall_spm._task_brk_set |
| 0x403f52f8 | vfs_state_mount_table_open_chain_probe_v1 |

Every one is a `table[k] = v` index-set shape.  Sites that have not trapped
in earlier boots simply never executed (the mount-table probe only runs on
the positioned-open error path, which Wall 8 made unreachable) or executed
the push path instead.

## Trigger in the Wall-9 boot

`g_vfs_positioned_close` → `fat32_close` (src/lib/nogc_async_mut/fs_driver/
fat32_owned_io.spl:9) unconditionally calls `fat32_sync_entry_size` for any
regular file with start_cluster >= 2 (a no-op size persist for a read-only
open) → that patches the file's directory entry and re-puts the directory
cluster it was read from — which is still in the cluster cache from the
open-time directory scan → cache-hit index-set arm → trap.

Lane workaround (NOT a fix): the Wall-9 streaming loader
(`arm_fs_exec_stream_payload_resident_v1`,
src/os/services/vfs/arm_fs_exec_vfs.spl) deliberately does not close the
positioned handle; one bounded virtual handle leaks per payload read (<= 3
reads across the R3-R5 rungs).

## Fix direction (compiler lane, same family as Wall 7)

Wall 7 fixed the sibling `arr.push(v)` stale-receiver store
(33336d214be, 1de2f3fe21c).  This is the index-set analogue: the aarch64
freestanding lowering of the index-set STATEMENT must not leave a trap as
the fall-through continuation when the callee returns.  Likely the same
MIR/ABI area (`lowering_expr_method.rs` / statement-position call
continuation).  Reproduce with any `table[k] = v; return` shape compiled
for aarch64-unknown-none and executed once.
