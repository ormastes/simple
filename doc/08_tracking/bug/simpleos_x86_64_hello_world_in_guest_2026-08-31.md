# SimpleOS x86_64 hello-world in-guest: what blocks each half (2026-08-31)

Goal: run hello world **on SimpleOS x86_64**, booted through **real firmware
(OVMF pflash -> GRUB-EFI -> multiboot1)** — never QEMU `-kernel`, never
`isa-debug-exit` — as (a) the Simple **interpreter** in-guest and (b) a
**natively-compiled binary** in-guest, each proven by the program's own console
output.

Gate: `scripts/check/check-simpleos-hello-world-in-guest-ovmf.shs`
(`--selftest` is fatal, 7 fixtures; the assembled QEMU argv is self-checked for
absence of `-kernel` and `isa-debug-exit`).

## B1 — 19 `src/os` modules fail HIR/MIR lowering under the Rust seed

`scripts/check/check-enterprise-store-in-guest-ovmf.shs` — an established
in-guest OVMF lane — **cannot build its kernel** on this tree:

```
FAIL — kernel build produced no build/os/simpleos_entstore_uefi128.elf
```

19 modules fail, dominated by one defect class:

| kind | count | example |
|---|---|---|
| `hir: cannot infer field type ... struct 'ANY' field '<f>'` | 11 | `executable_admission_pipeline.spl` field `load_ranges` |
| `codegen: N function bodies failed to compile` | 5 | `vfs.spl`, `rt_net_socket_facade.spl`, `userlib/fs.spl` |
| `mir: unknown variant or method on enum` | 1 | `server_launch_grants.spl` / `CapabilityKind.NetSocketCreate` |

Failing files (all under `src/os`): `kernel/loader/{cpio_newc,
executable_admission_pipeline, executable_arm32_mapping_owner_v1,
executable_authority_registry, executable_x86_32_mapping_owner_v1,
riscv32_fs_exec_spawn, riscv32_sv32_mapping_owner_v1, server_launch_grants,
x86_32_fs_exec_spawn}`, `kernel/net/rt_net_socket_facade`,
`kernel/scheduler/{scheduler_arm32_executable_adoption_v1,
scheduler_executable_adoption, scheduler_riscv32_executable_adoption_v1,
x86_32_mapping_adoption_reservation_v1}`, `services/netstack/netstack_init`,
`services/vfs/{arm_fs_exec_vfs, vfs, vfs_boot_state, vfs_write_ops}`,
`userlib/fs`.

**Root cause (checked, not assumed): these are stale SOURCE idioms that newer
seeds now reject as HARD errors, not a seed regression to wait out.** Two
classes, both mechanically fixable:

1. **Field access on an erased receiver.**
   `executable_admission_pipeline.spl:367` is
   `authoritative_inputs.verified_load_ranges = layout.unwrap().load_ranges`.
   `unwrap()` returns `ANY`, so `.load_ranges` has no struct to resolve against
   — exactly the documented limitation in `.claude/rules/language.md`
   ("Chained methods on erased receivers ... Workaround: intermediate typed
   `val`"). Fix: `val l = layout.unwrap()` then `l.load_ranges`. Same shape for
   `filesystem_name`, `has_entry_identity`, `sockets`, `_pin`, `mount_index`,
   `executable_adoption_state`.
2. **Paren-less accessor on a builtin container.** Confirmed live on a sibling
   script in this same session: `scripts/os/fsexec_mkimg_simple.spl:44` used
   `s.length` and the seed refused with
   *"paren-less accessor on a builtin container. Use the method form (e.g.
   `.len()`) instead. This is a hard error in every lane"*. **Fixed in this
   change** (`s.length` -> `s.len()`), after which the FAT32 image writer runs
   clean. The same wording appears in the `src/os` failures.

So the owner of B1 is whoever repairs `src/os`, not the compiler lane. The
files are unchanged at `origin/main`, i.e. the tree has been carrying these
idioms since before the enforcement tightened.

### B1 is NOT bypassable by `SIMPLE_ALLOW_STUB_FALLBACK` (measured)

The failing modules print *"set SIMPLE_ALLOW_STUB_FALLBACK to emit empty stubs
instead"*, which invites the obvious workaround. **It does not work**, and the
reason is worth recording so nobody spends another build cycle on it:
`SIMPLE_ALLOW_STUB_FALLBACK` rescues **codegen body** failures (one function
becomes a 0-returning stub); it cannot rescue a **HIR/MIR module-level**
failure, because lowering aborts before there is a body to stub.

Measured, both with the 08-31 seed, `--source src/os` (the whole tree is
compiled regardless of entry reachability):

| run | flags | result |
|---|---|---|
| 1 | defaults | `native-build aborted: 30 file(s) failed to compile` (18 lowering + 12 modules hitting the 300s per-file default on a loaded box) |
| 2 | `SIMPLE_ALLOW_STUB_FALLBACK=1`, `--timeout 1200` | `native-build aborted: 18 file(s) failed to compile` — timeouts gone, **every lowering failure remains** |

The 17 distinct defects, in 16 files:

- `struct 'ANY' field ...` (erased receiver, mechanical fix — typed
  intermediate `val`): `load_ranges` x3, `has_entry_identity` x2,
  `filesystem_name`, `sockets`, `_pin`, `mount_index`
- named-struct field-type inference: `ExecutableImageHandleV1.filesystem_name`
  x2, `Scheduler.executable_adoption_state` x2,
  `MessageQueue.owned_payload_bytes`
- **not mechanical — semantic decisions for the owning lane, do not guess:**
  - `TaskCapRecord` field `session_id` **does not exist**
    (declared fields: `task_id, caps, unveil_paths, is_unveiled`) —
    `src/os/kernel/ipc/capability.spl`
  - `CapabilityKind` has no variant `NetSocketCreate` —
    `src/os/kernel/loader/server_launch_grants.spl`

Because the two semantic defects also abort their modules, **partial mechanical
repair does not unblock the build** — the fix has to cover all 17.

Note how many are for OTHER architectures (arm32, riscv32, x86_32) yet still
block an **x86_64** entry: `native-build` compiles every file under `--source`,
so `--entry-closure` does not spare an entry from unrelated arch modules. That
is itself worth fixing — it means any one arch's rot blocks all of them.

Seeds tried (all Rust seeds; the pure-Simple self-hosted compiler cannot compile
anything yet — `hir codec: no Visibility arm for tag -1`):

| seed | date | result |
|---|---|---|
| `worktrees/simple-main/.../target/release/simple` | 08-27 | **parse** failure: `scheduler_types.spl:116:9 expected Indent, found Underscore` (a multi-line `if ... or` continuation) |
| `worktrees/goal-bootstrap/...` | 08-28 | not run |
| `worktrees/phase1-dom-color-fcmp/...` | 08-29 | running |
| `/mnt/data/phase1-identity-origin-main/...` | 08-31 | parses, then the 19 lowering failures above |

## B2 — the x86_64 ring-3 spawn API has no reachable entrypoint

`examples/09_embedded/simple_os/arch/x86_64/fs_exec_prod_ring3_entry.spl` and
`fs_exec_general_ring3_entry.spl` both import

```
use os.kernel.loader.x86_64_fs_exec_ring3.{x86_64_fs_exec_enter_image_ring3}
```

**That function does not exist anywhere in `src/os`, at any revision reachable
from `origin/main`.** `src/os/kernel/loader/x86_64_fs_exec_ring3.spl` is 619
lines and declares **zero** `pub fn`; its only handoff driver is the private
`_x86_64_fs_exec_enter_ring3` (line 452). Both entries are therefore dead.

The public facade that does exist,
`src/os/kernel/loader/x86_64_fs_exec_spawn.spl`, now **fails closed for
path-only callers** by design (`x86_64_fs_exec_spawn*` -> `fs_exec_spawn_as`,
"a path is not execution authority"); the authenticated route requires an
`ExecutableAuthorityRegistryV1` + token + `ExecutableLoadConsumerV1`, and the
modules implementing that route are exactly the ones failing in B1.

**Workaround used by this lane:** the new entry
`examples/09_embedded/simple_os/arch/x86_64/hello_world_ovmf_entry.spl` carries
the proven private helpers (`_admit_raw_elf64`, `_map_pt_loads`,
`_build_sysv_stack_frame`, `_x86_64_fs_exec_enter_ring3`) **in-file**, so it
depends only on `pmm` / `vmm` / `arch_adapt.x86_64_user_entry` / `boot.mmio` —
none of which are in the B1 failure set. This is a lane-local workaround, not a
fix; the right fix is to export a public wrapper (or repair the authenticated
pipeline).

## B2b — `_text_z_size` silently STUB-FALLBACKs, corrupting every argv frame

`src/os/kernel/loader/x86_64_fs_exec_ring3.spl:91` writes

```
fn _text_z_size(value: text) -> u64:
    val bytes = unsafe(capabilities: [ffi]):
        rt_text_to_bytes(value)
    (bytes.len() as u64) + 1
```

Under freestanding codegen the seed reports
`GlobalLoad: unresolved identifier 'bytes' (not a global, function, const-data
name, or import)` — the `val NAME = unsafe(...): expr` binding form does not
survive lowering — and then **STUB-FALLBACKs the whole body to a 0-returning
stub**. `_text_z_size` is what `_build_sysv_stack_frame` uses to size argv[0],
argv and envp, so every ring-3 process built through that path gets a silently
mis-sized SysV startup frame. There is no link error and no runtime diagnostic;
it presents as an inexplicable ring-3 fault or a bad `argc` readback.

Fix (applied in this lane's copy, still open in `src/os`): bind at statement
level — `val bytes: [u8] = rt_text_to_bytes(value)`.

**Is this the same defect as `nil_into_non_optional_struct_field_invalid_heap_2026-08-31.md`?
No — checked, not assumed.** That bug is a *value* defect: a field is
constructed holding an invalid heap value that compares `!= nil`, so runtime
guards pass and native deref SIGSEGVs. B2b is a *name-resolution* defect at
codegen time, and the seed says so literally:
`GlobalLoad: unresolved identifier 'bytes' (not a global, function, const-data
name, or import)` — the binding `bytes` never enters scope at all, so there is
no value of any kind to be wrong. The two share a **failure-mode family**
(silent degradation instead of failing closed: one degrades a body to a
0-returning stub, the other degrades a type error to a poisoned value), but not
a mechanism. Fixing one will not fix the other.

The shared, actionable lesson is the STUB-FALLBACK policy itself: a body that
fails to compile becomes a stub that returns 0 with no link error and no runtime
diagnostic. For a size-computing function feeding a stack-frame builder that is
indistinguishable from correct behaviour until the guest faults.

## B3 — interpreter-in-guest needs `bin/release/x86_64-unknown-simpleos/simple`

The interpreter half is **not** unimplemented — the lane already exists:

- `scripts/os/ssh_simple_hello_uefi.shs` (OVMF -> GRUB-EFI -> multiboot1, then
  `ssh root@host /usr/bin/simple simple /hello.spl`)
- `scripts/os/fsexec_mkimg_simple.spl` (stages the guest `simple` binary at
  `/usr/bin/simple` + `/FSEXEC.ELF`, and `/hello.spl`)

It requires the artifact `bin/release/x86_64-unknown-simpleos/simple`, which is
not present in this tree, plus `sshpass`. Producing that artifact needs a
working `src/os` kernel + tool build — i.e. it is **downstream of B1**.

## Status

- Boot chain (OVMF pflash -> GRUB-EFI -> multiboot1): reused verbatim from the
  entstore lane; no `-kernel`, no `isa-debug-exit`, argv self-checked.
- Native hello payload: **built** —
  `build/os/hello/HELLO.ELF`, ET_EXEC x86_64, no PT_INTERP, entry `0x400000`,
  written in Simple (`build/os/hello/src/hello_user_entry.spl`) and compiled by
  the **Rust seed**, with a minimal ring-3 Simple runtime in
  `build/os/hello/src/boot/user_stubs.c` (bump heap, `rt_string_new*`,
  `rt_print`, `serial_println`, `exit(2)` via syscall 0 — no `isa-debug-exit`).
- Native hello in-guest execution: **BLOCKED at the kernel build (B1).** Nothing
  was booted; there is no serial transcript, and none is claimed.
- Interpreter in-guest: blocked on B3, which is blocked on B1.

Gate lands **ADVISORY/RED**. Its literal verdict today:

```
ERROR — nothing was checked: kernel build produced no
build/os/hello/simpleos_hello_uefi128.elf — Build failed: native-build aborted:
18 file(s) failed to compile (B1: src/os modules fail HIR/MIR lowering;
SIMPLE_ALLOW_STUB_FALLBACK cannot bypass module-level lowering failures.)
```

exit 2 — deliberately **ERROR, not FAIL**: zero programs were executed in-guest,
and FAIL would wrongly imply something ran and misbehaved.

`--selftest` is green (7 fatal fixtures), so the gate itself is known-good and
will start reporting real rungs the moment B1 clears — it is red about the
world, not about itself.

## Promotion criteria

Promote from ADVISORY to MANDATORY when all of the following hold:

1. B1's 17 defects are repaired and `native-build` produces
   `build/os/hello/simpleos_hello_uefi128.elf`.
2. The gate's lane call-path stub check stays silent (no function this lane
   calls was stub-fallbacked). This check is already live and was validated
   against the real pre-fix build log: it flags `_text_z_size` and ignores the
   7 irrelevant stubs.
3. All 7 serial rungs go green, L6 being the program's own output
   `HELLO_NATIVE_SIMPLEOS_X86_64_OK`.
4. The interpreter row is either green or still explicitly ADVISORY via B3.
