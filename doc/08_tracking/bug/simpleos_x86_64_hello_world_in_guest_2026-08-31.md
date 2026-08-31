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

---

## 2026-08-31 (later session): B1 confirmed fixed; five further blockers found

Base: `goal/simpleos-b1-merge-clobber-restore-20260831` @ `91b6b9f28dd`.
Compiler for every artifact below: the **Rust seed**, rebuilt from that base at
`/mnt/data/.cargo-target-hello-lane/release/simple` (60,949,888 bytes,
`Simple Language v1.0.0-rc.1`). The pure-Simple self-hosted compiler is still
unusable (`hir codec: no Visibility arm for tag -1`), so it produced nothing.

**Recovery note.** None of this lane had ever been committed. The gate, both
builder scripts, the two entry sources and this record existed only in an
unpushed worktree; they are absent from `origin/main`, from the base branch,
and from `git log --all`. They are now committed.

### B1 is fixed
`SIMPLE_ALLOW_STUB_FALLBACK=0` now yields **zero Simple-module compile
failures** (was "18 file(s) failed to compile"). The build reaches the link
stage. Everything below is a *different* bug that B1 was masking.

### B4 — linker script named a module layout that no longer exists (FIXED)
All 66 assignments in `linker_128mb.ld` pointed at
`kernel__abi__syscall_shim__spl_handle_*`. The shims were long ago split into
`syscall_shim_{process,ipc,file,net,device,...}` and the seed emits a `src__os__`
prefix, so the real names are e.g.
`src__os__kernel__abi__syscall_shim_process__spl_handle_exit`. Every RHS
resolved to nothing and `ld.lld` failed the link outright. Same staleness class
as the B1 facade re-exports, but in the linker script — which is why the
previous lane never got past it.
Regenerated mechanically from `nm` over the kernel objects: **88 aliases are
actually referenced, all 88 resolve unambiguously, 0 missing, 0 ambiguous.**
Switched to `PROVIDE()`, because a plain `foo = missing;` is a hard error even
when nothing references `foo` — that made the script brittle against
`--entry-closure` pruning. `spl_x86_dispatch_installed_syscall_abi` is
referenced by nothing in this closure and is no longer force-assigned.
NOTE: this script is shared with the SSH lane, which carried the same latent
link failure.

### B5 — FAT32 image writer used a stale paren-less accessor (FIXED)
`scripts/os/fsexec_mkimg_simple.spl:44` used `s.length` on a builtin text. The
seed refuses it under `SIMPLE_JIT_STRICT`:
`cannot infer field type while lowering _pad_ascii: struct 'String' field 'length'`.
That aborted the gate with ERROR before any VM started. Fixed to `s.len()`;
the padding is ASCII-only FAT32 8.3, so bytes-vs-chars does not bite.

### B6 — one-word typo dropped 3,600 lines of weak stubs (FIXED)
`baremetal_stubs.c:3662` called `x86_64_collector_nonce_slot_line_length`,
declared nowhere; line 3649 calls the real `x86_64_nonce_slot_line_length` with
the same arguments. The whole file therefore failed to compile, dropping every
weak stub it defines; their references resolved to 0 and the kernel booted to
`[BOOT64] idt` then faulted repeatedly at low addresses. After the fix the
kernel grew 438,392 -> 2,062,448 bytes and **L2 went green**.

### B7 — high-MMIO window never mapped at its higher-half VA (FIXED)
`crt0.s` identity-maps the 1 GiB PCIe MMIO window at `0xC000000000` via
PML4[1]/PDPT[256]. But `baremetal_stubs.c:1937` translates BAR0 to
`NVME_BAR_VIRT_BASE + (phys - NVME_BAR_PHYS_BASE)` = `0xFFFFC00000000000 + off`.
Nothing maps that VA at NVMe-init time: the comment claims "present under user
cr3", but NVMe init runs long before `create_user_address_space`, on crt0's own
`boot_pml4`. Literal evidence:

```
[nvme-c] BAR0=0xffffc00000004000 (phys=0xc000004000)
[fault] rip=0x0000000008004cbe
[fault] cr2=0xffffc0000000401c        <- BAR0 + 0x1c (CSTS)
[fault] cr3=0x000000000819e000        <- = boot_pml4, inside the kernel image
[fault] *** END FRAME (recovering) ***   (forever)
```

`0xFFFFC00000000000` decodes to PML4[384], PDPT[0]. Added exactly those two
entries, aliasing the same `boot_high_pd` — no extra page-table memory, identity
map untouched. **L3 went green**: NVMe now reports CAP, admin queues, and
`NS1: sectors=1833, sector_size=512`.

### B8 — `rt_file_write_bytes` writes 3 bytes and returns true (OPEN)
Blocking L4. The gate builds the guest FAT32 volume by concatenating a
structural prefix with the payload. The writer reports
`prefix_bytes=381440` but `build/os/elfexec_simple/fat32-simple-prefix.bin` is
**3 bytes** on disk, so sector 0 of the guest disk is `08 00 00` followed by the
raw ELF instead of a FAT32 boot sector:

```
[nvme-c] Sector 0 read OK, first bytes: 08 00 00 7F 45 4C 46 02 01 01 00 00 00 00 00 00
[nvme-c] FAT32 signature at offset 510: 0x0x0
[hello] FAIL fat32 open /FSEXEC.ELF rc=-1
```

Minimal reproducer (interpreter path, `simple run`): a 4-element array built by
`push` and an 8-element array from `rt_byte_array_new_len` both write the SAME
3 bytes `08 00 00`, while the arrays themselves read back correctly
(`c len=8 c0=235 c7=170`) and the call returns `true`. So the arrays are fine
and the defect is in `rt_file_write_bytes` argument marshalling/dispatch, not in
the caller. Ruled out by inspection: the handler body
(`interpreter_extern/file_io.rs:1540`), `value.rs:1838 byte_array_view`, and
`extract_path`. Strong lead: `codegen/runtime_sffi.rs:2045` declares
`rt_file_write_bytes` with FOUR i64 params (ptr,len,ptr,len) while the
interpreter handler expects TWO `Value`s — an arity/marshalling mismatch that
would explain a 3-byte payload.

### Still-open C defects (pre-existing, all OFF the hello call path)
Not fixed; none is reachable from this entry.
- `tls13_aes256_gcm_helper.c:86,94,101` — `x86_aes_repack_bytes` used 3x,
  defined and declared nowhere. Same class as the `rt_unwrap_or_trap` incident.
- `runtime_service_owners.c:65` — `no member named 'gc_flags' in 'HeapHeader'`
  and `use of undeclared identifier 'BAREMETAL_GC_BYTE_PACKED'`.
- `up2_dci_uefi_loader.c:1` — `efi.h` not found; external gnu-efi SDK is not
  installed here. Legitimate SKIP, not a defect.

### Rung status (real OVMF pflash boot; never `-kernel`, never isa-debug-exit)
| rung | | status |
|---|---|---|
| L1 | `[grub-uefi] multiboot loading` | **OK** |
| L2 | `SimpleOS x86_64 hello-world in-guest` | **OK** |
| L3 | `[hello] nvme online` | **OK** |
| L4 | `[hello] /FSEXEC.ELF read size=` | MISS — blocked by B8 |
| L5 | `[hello] entering ring 3` | MISS |
| L6 | `HELLO_NATIVE_SIMPLEOS_X86_64_OK` | MISS |
| L7 | `[hello] native program exited rc=0` | MISS |

Gate verdict, honestly RED:
`FAIL — 1 program(s) staged, 7 rung(s) checked, missing: L4 L5 L6 L7;`
`interpreter row ADVISORY/RED: no in-guest Simple interpreter exists in this tree`

### Interpreter row — still ADVISORY/RED
`bin/release/x86_64-unknown-simpleos/simple` exists nowhere on this host and
`build/os/sysroot/lib/` is absent. Producing it needs the LLVM sysroot plus a
full `simpleos-native-build.shs` of `src/compiler`+`src/lib`+`src/app`, behind a
Stage2 admission-receipt check. Not attempted this session; L6-equivalent for
the interpreter row was NOT reached and must not be claimed.

---

## B8 RESOLVED, B9 found (same session, later)

### B8 — RESOLVED: an extern declaration suppressed the SFFI alias
Root cause was NOT in `rt_file_write_bytes` itself. `compile_call`
(`codegen/instr/calls.rs`) decided whether to apply the SFFI alias table
(`rt_file_write_bytes` -> `rt_file_write_bytes_array`) using
`ctx.func_ids.contains_key(name)`. `func_ids` **also holds `extern fn`
DECLARATIONS**, registered with `Linkage::Import`. So a user declaring the
runtime symbol as an extern counted as "a user function shadowing the builtin",
the alias was suppressed, and codegen emitted a direct call to the raw symbol
under the SFFI convention: a `text` arg split into `(ptr, len)` plus the array
value = **3 arguments against the 4-argument C ABI**
`rt_file_write_bytes(path_ptr, path_len, data_ptr, data_len)`. The length came
from a stale register (constantly 3), which is why every call wrote the same 3
bytes and still returned true.

This was **general to every alias in the table** (`rt_file_read_text`,
`rt_file_delete`, `rt_dict_insert`, ...) whenever a user declares that runtime
symbol extern — not specific to this one function.

Fix (one line): use the existing `has_defined_local_function` predicate, which
tests `Linkage != Import`. A real `fn len` body is still defined-local and still
shadows, so the `module_fn_shadowed_by_builtin_name_2026-08-21` fix is
preserved.

Effect: the guest volume is now a real FAT32 filesystem. Sector 0 is
`EB 58 90 "SIMPLEOS"` with the `55 aa` signature, and the in-guest driver parses
the BPB correctly:
`[fat32-c] BPS=0200 SPC=40 reserved=20 FATs=01 FAT_size=09 root_cluster=02 data_start=29`

### B9 — OPEN: `text[i] as u8` yields 0 when `i` is a u64 VARIABLE
Now blocking L4. The root directory entries are written with the correct
cluster and size but **blank 8.3 names**: the entry for the payload carries
cluster `0x000d` (13) and size `0x1ae8` (6888) — both correct — while its
11-byte name field is all `00`/`20`. `[hello] FAIL fat32 open /FSEXEC.ELF rc=-1`
follows, because the guest cannot match a nameless entry.

Minimal reproducer (`simple run`, JIT/Cranelift path):
```
fn _pad_ascii(s: text, width: u64) -> [u8]:
    var out: [u8] = []
    var i: u64 = 0u64
    while i < width:
        if i < s.len():
            out.push(s[i] as u8)
        else:
            out.push(0x20u8)
        i = i + 1u64
    out
_pad_ascii("FSEXEC", 8u64)
```
OBSERVED `pad=0 0 0 0 0 0 32 32` — EXPECTED `pad=70 83 69 88 69 67 32 32`.
The `0x20` padding is correct, so the loop, the bounds test and `push` all work;
only `s[i] as u8` with the u64 loop variable produces 0. Indexing with a
LITERAL is fine: a separate probe gives `s[0] as u8 = 70` ('F') and
`s.bytes()[0] = 70`.

Silent zero rather than a diagnostic is the dangerous part: it produced a
structurally valid filesystem whose files are simply invisible.

NOTE for whoever fixes it: `text` here is documented as `.len()` counts BYTES
while `[]` indexes CHARS. Preserve that contract; do not resolve this by
redefining either.

---

## B9 RESOLVED, B10 RESOLVED, B11 OPEN — L1..L5 now green

### B9 — RESOLVED: heap-boxed u64 rejected as an index (runtime, general)
Root cause was NOT `text`-specific and NOT the `as u8` cast. `rt_index_get` /
`rt_index_set` gated every non-dict receiver on `RuntimeValue::is_int()`, i.e.
`tag() == TAG_INT`, the **inline 61-bit signed** form only. But
`RuntimeValue::from_u64` **always heap-boxes** into `HeapObjectType::UInt`
(`core.rs:387`), a `TAG_HEAP` value. So any `u64`/`usize`-typed index failed the
test and the function silently returned `NIL`; the index expression produced
nil and `as u8` on nil gave 0.

Narrowing table that pinned it:

| shape | result |
|---|---|
| `s[0]` literal | 70 OK |
| `s[i64var]` | 70 OK |
| `s[u32var]` | 70 OK |
| `s[u64var]` (var AND val) | **nil** BROKEN |
| `s[u64var].to_text()` | `nil` — the char itself is nil, not a cast bug |
| `arr[u64var]` | 11 OK — a typed MIR fast path bypasses `rt_index_get` and MASKED the defect |

The array/tuple generic paths were equally broken; arrays only *looked* fine.
Fix adds `RuntimeValue::as_index_i64()` (inline `TAG_INT`, heap `HeapInt`, heap
`HeapUInt` via `i64::try_from`) as the single shared decode point, used by both
functions. Negative indices, the tuple `idx >= 0` guard, `char_at` string
behaviour and the `.len()`=bytes / `[]`=chars contract are all unchanged.
`cargo test -p simple-runtime`: 1225 passed, 1 pre-existing/flaky failure
(`value::sffi::file_io::…fail_closed`, passes in isolation with and without the
change, fails only under the full parallel suite).

Effect: 8.3 names are now written correctly — `strings` on the image shows
`HELLO   SPL`, `FSEXEC  ELF`, `BIN`, `USR`, `ETC`, `TMP`, `HOME`.
**L4 went green**: `[hello] /FSEXEC.ELF read size=6888 buf=0x1209897344`.
**L5 went green**: `[hello] entering ring 3 ...`

Suspected sibling defect, NOT fixed, needs its own reproducer:
`compile_slice_op` (`codegen/instr/collections.rs:~380`) passes slice
start/end/step as raw i64 vreg values to `rt_slice`, so a `u64`-typed slice
bound would hand a boxed pointer through as a raw integer.

### B10 — RESOLVED: payload segments shared a page, so W^X admission refused it
`[spawn] FAIL raw ELF admission rejected`. The kernel maps one frame per page
and UNIONS the permissions of every segment covering that page, so
`_admit_raw_elf64` rejects an image where an executable and a writable segment
share a page — the PTE would silently become W+X. `user.ld` had no alignment
between groups, so `.text` (RX, ending `0x4004b0`) and `.bss` (RW, starting
`0x400500`) both landed in page `0x400000`. Byte ranges disjoint, same page,
correctly refused.

`ALIGN(0x1000)` before `.rodata` and `.data` gives
`0x400000 RX / 0x401000 R / 0x402000 RW`. Admission now passes:
`[spawn] parsed entry=0x4194304`.

Note this is the payload's linker script only; the kernel's check was right and
is unchanged.

### B11 — OPEN: `vmm_clone_kernel_low_private` refuses the new user AS
Now the only blocker for L6/L7. Serial:
```
[VMM] PML4 at physical 0x335609856
[VMM] Identity-mapped 4GB with 2MB pages (2048 entries)
[hello] pmm+vmm online
[hello] entering ring 3 ...
[spawn] parsed entry=0x4194304
[spawn] FAIL clone kernel low private root=335634432
[hello] native program exited rc=-1
```
`vmm_clone_kernel_low_private` (`src/os/kernel/memory/vmm_address_space.spl:147`)
has exactly three refusal branches: `vmm_kernel_pml4_phys() == 0`; the kernel's
PML4[0] not present; or `_clone_table` failing its page allocation. The function
returns a bare bool, so the serial line cannot distinguish them. Lane-local
diagnostics added to the entry (printing `kpml4` and PML4[0]) to settle it in
one rebuild; result not yet available.

Relevant context: this lane boots via GRUB multiboot1, so there is no Limine
HHDM (`[BOOT] WARNING: No HHDM response from Limine`), and `_phys_to_virt` is
`phys + _vmm_hhdm_offset`. The earlier fault frames showed `cr3=0x819e000`
(crt0's `boot_pml4`) while the Simple VMM built its own PML4 at `0x14024000`
— worth checking whether `_vmm_pml4_phys` refers to the table the CPU is
actually on.

### Rung status (real OVMF pflash; never `-kernel`, never isa-debug-exit)
| rung | | status |
|---|---|---|
| L1 | `[grub-uefi] multiboot loading` | **OK** |
| L2 | `SimpleOS x86_64 hello-world in-guest` | **OK** |
| L3 | `[hello] nvme online` | **OK** |
| L4 | `[hello] /FSEXEC.ELF read size=` | **OK** |
| L5 | `[hello] entering ring 3` | **OK** |
| L6 | `HELLO_NATIVE_SIMPLEOS_X86_64_OK` | MISS — blocked by B11 |
| L7 | `[hello] native program exited rc=0` | MISS |

Gate verdict, honestly RED:
`FAIL — 1 program(s) staged, 7 rung(s) checked, missing: L6 L7;`
`interpreter row ADVISORY/RED: no in-guest Simple interpreter exists in this tree`

### Note on the two seed defects
B8 and B9 are **general Rust-seed defects surfaced by this lane**, not
SimpleOS-specific. Both fail SILENTLY — B8 wrote 3 garbage bytes and returned
true; B9 yielded nil and then 0. Any Simple program doing the same operations
was equally affected. That is why they survived until something as demanding as
booting an OS surfaced them.

---

## B11 RESOLVED, B12 OPEN — L1..L5 green, ring-3 handoff triple-faults

### B11 — RESOLVED: the VMM impl that runs never published its kernel PML4
The added diagnostic settled it in one build: `[spawn] clone-diag kpml4=0` —
the FIRST refusal branch, not the page-table walk.

THREE VMM implementations print byte-identical banners
(`[VMM] PML4 at physical ...`): `vmm_core.spl:318`, `vmm.spl:259`, and
`arch/x86_64/paging.spl:238`. The serial log cannot tell you which one ran.
`vmm_core.spl:268` already documents this hazard and ships the remedy,
`vmm_publish_kernel_pml4`, whose docstring predicts exactly this failure:
"every FS-exec ring-3 spawn hit the guard and failed the spawn with rc=-1".

`paging.spl:236` calls it. **`vmm.spl` did not** — and `vmm.spl:vmm_init` is
what the hello entry calls (`use os.kernel.memory.vmm.{vmm_init}`). It wrote
only the STRUCT global `g_vmm.pml4_phys`, while every address-space consumer
(`create_user_address_space`, `vmm_clone_kernel_low_private`, `vmm_copy`) reads
the SCALAR `_vmm_pml4_phys` via `vmm_core.vmm_kernel_pml4_phys()`. So the
scalar stayed 0 after a fully successful init.

Fix: call `vmm_publish_kernel_pml4(pml4_phys, hhdm_offset)` from
`vmm.spl:vmm_init`, mirroring `paging.spl:236`, using the LOCAL `pml4_phys`
(struct globals are the unreliable category under freestanding codegen).
Confirmed by `[VMM] portable VMM published kernel PML4 0x335609856` on serial.

**Diagnosability fixed permanently.** `vmm_clone_kernel_low_private` returned a
bare bool, so every diagnosis needed a fresh kernel build to learn which of its
three refusals fired. It now names the branch on the serial log — silent on the
success path, explicit on failure. The lane-local probe was removed as
superseded.

Effect — the whole spawn path now works:
```
[spawn] user AS ready (private low) root=335634432
[spawn] phoff=64 phentsize=56 phnum=4 use_stream=0
[spawn] image span lo=0x4194304 hi=0x5320704
[spawn] PT_LOAD segments mapped
[spawn] frame argc readback=1 expected=1
[spawn] user stack mapped top=0x549757911040 pages=2048 rsp=0x549757910912
[spawn] entering user cs=0x2b iopl=3 rip=0x4194304 rsp=0x549757910912
ABC
```
(Those span/rip values print DECIMAL despite the `0x` prefix: 4194304 = 0x400000.)

### B12 — OPEN: `iretq` into CPL3 triple-faults; VM halts
`ABC` is NOT program output. A/B/C are kernel-side progress markers inside
`examples/.../boot/enter_user_first.s` (lines 60, 79, 102); `C` is emitted
immediately before the `iretq` that performs the hardware CPL transition —
its own comment says so. So the kernel reaches the final handoff and the user
program produces nothing.

Evidence that this is a triple fault rather than a hang or a truncated capture:
- The serial log ends mid-stream at `ABC` with NO trailing newline, and no
  further kernel output of any kind.
- The gate passes `-no-reboot` (line 280), so a triple fault stops the VM
  instead of resetting it — consistent with the abrupt end and with the ABSENCE
  of a second OVMF banner.
- The whole log contains exactly ONE `EXCEPTION FRAME`, from early boot. The
  rich fault hook demonstrably works (it printed many frames during the B7
  investigation), so nothing caught a fault after `C`: the fault escalated
  rather than being handled.

Prime suspects, in order:
1. The user PT_LOAD pages or an intermediate level lack `US=1`, so the very
   first instruction fetch at CPL3 faults; the handler then cannot run under
   the user cr3 and it escalates. Note `vmm_clone_kernel_low_private` sets
   `PTE_USER` on the cloned PML4[0] entry, but every level down to the leaf
   must also carry it.
2. TSS `rsp0` / IST stack not mapped in the user address space, so the CPU
   cannot even push an exception frame -> double -> triple fault. `[tss] rsp0
   installed sel=0x30` appears BEFORE the user AS is created.
Neither is confirmed; both need a page-table dump under the user cr3 at the
moment of handoff, which is another build cycle.

The payload itself is exonerated: it is the current 13800-byte ELF (read size
matches), carries the marker, has correct page-separated RX/R/RW segments, and
its `_start` sets up its own `.bss` stack inside a mapped RW page.

### Rung status (real OVMF pflash; never `-kernel`, never isa-debug-exit)
| rung | | status |
|---|---|---|
| L1 | `[grub-uefi] multiboot loading` | **OK** |
| L2 | `SimpleOS x86_64 hello-world in-guest` | **OK** |
| L3 | `[hello] nvme online` | **OK** |
| L4 | `[hello] /FSEXEC.ELF read size=` | **OK** |
| L5 | `[hello] entering ring 3` | **OK** |
| L6 | `HELLO_NATIVE_SIMPLEOS_X86_64_OK` | MISS — blocked by B12 |
| L7 | `[hello] native program exited rc=0` | MISS |

Gate verdict, honestly RED — the lane is landed RED, not weakened to green:
`FAIL — 1 program(s) staged, 7 rung(s) checked, missing: L6 L7;`
`interpreter row ADVISORY/RED: no in-guest Simple interpreter exists in this tree`
