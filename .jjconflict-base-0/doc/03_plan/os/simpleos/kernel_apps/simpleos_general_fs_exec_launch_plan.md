# SimpleOS Registry-Free Filesystem-General Exec — Launch Plan (x86_64 first, ARM parity noted)

Status: ready to execute. Owner: kernel/loader. QEMU boot is run by the human main agent.

## 1. Goal + Success Criteria

Make **any** ELF file on the SimpleOS filesystem launchable **purely by PATH** through the shell, with
**no** app registration, **no** SMF-name allowlist, and **no** fake-pid placeholder. Drop an ELF at an
arbitrary path → `shell_exec` PATH-resolves it → the loader reads the raw on-disk bytes into an
identity-mapped buffer → maps its `PT_LOAD` segments into a fresh user address space → builds a SysV
AMD64 ring-3 stack (with a real `argc/argv/envp/auxv` frame) → `iretq`s to CPL3 → the program runs and
exits. **Success proof** mirrors the existing harness: the self-terminating QEMU run emits, on serial,
`[spawn] image path=… entry=0x… segments=N`, then `FDR` (ring-3 `out`, only reachable at CPL3), then
`FSEXEC_OK rc=42` (via `syscall 60`), then exits QEMU via `out 0xf4`. Pass = all three markers present
for an ELF launched through the **shell PATH** at a path that is **not** in any alias table or registry.

## 2. Confirmed Root Cause

Two coupled defects keep the shell from ever reaching the proven ring-3 handoff for an arbitrary file
(every refutation lens converged on exactly these):

1. **Shell never reaches the arch handoff (phantom-pid generic path).**
   `src/os/apps/shell/exec.spl:40` calls the arch-neutral `fs_exec_spawn`
   (`src/os/kernel/loader/fs_exec_spawn.spl:240`), whose `fs_exec_prepare_spawn`
   (`fs_exec_spawn.spl:234`→`203` `fs_exec_prepare_spawn_from_bytes`) only calls
   `build_user_process_image_unchecked` (`:211`) + `scheduler_create_bootstrap_user_task_pid` (`:220`)
   and returns `prepared.pid`. It **never maps PT_LOADs and never enters ring 3** — it registers a
   bootstrap TCB and hands back a phantom pid. The real map+`iretq` sequence
   `x86_64_fs_exec_enter_image_ring3` is reached **only** from `x86_64_fs_exec_spawn_as`
   (`x86_64_fs_exec_spawn.spl:168`), which the shell path never calls.

2. **`raw_blob=0` fail-closed on every registry-free branch (boxed-`[u8]` hazard).**
   `x86_64_fs_exec_spawn_as` already routes into the ring-3 handoff and already fails-closed instead of
   returning a phantom pid (`x86_64_fs_exec_spawn.spl:167-178` — this part is DONE). But the blob it
   passes comes from `_x86_64_read_spawn_bytes_and_blob` (`:96-107`), which returns a **nonzero**
   `raw_blob` on only two branches: `_x86_64_try_static_fat32_exec` (`:97-99`, the hardcoded SMF-name
   allowlist `_x86_64_static_fat32_alias` at `:16-41`) and `_x86_64_try_fat32_exec_alias` (`:100-102`,
   the `app_registry`) — **exactly the two mechanisms the goal forbids**. The cache branch (`:103-105`)
   and the genuinely-general `g_vfs_read_executable_bytes` branch (`:106-107`) both hardcode
   `(bytes, 0.to_u64())`. With `raw_blob=0`, `x86_64_fs_exec_handoff_blob_ready` (`:109-110`) is false →
   `handoff_rc=-5` (`:170`) → return -5 (`:178`). The handoff is never entered.
   This is unrecoverable by passing the boxed `[u8]` instead: freestanding native-build stores `[u8]`
   as boxed RuntimeValues, so an ELF header read off `image.file_bytes` yields `magic≈248, phoff=16`
   (`x86_64_fs_exec_ring3.spl:49,178-193`). The handoff **must** parse via `mmio_read*` off a
   pre-sized, contiguous, **identity-mapped raw buffer** whose pointer is nonzero.

3. **Placeholder must be retired.** `_x86_64_spawn_static_seeded` (`x86_64_fs_exec_spawn.spl:50`) with
   `_x86_64_static_stub_size` (`:43`, hardcoded 273/274) fabricates a pid and prints fake
   `entry=0 segments=1 stub_bytes=…` lines **without loading anything**. It is taken on the wine_hello
   shortcut (`:128`) and as fallback when bytes ≤ 4 (`:132`) or SMF-stub extraction fails (`:143`). For
   general exec it must fail-closed, never fabricate success.

**The proven seam that fixes (2):** the verification harness already reads an arbitrary path into the
identity-mapped buffer with `simpleos_fat32_stream_open(path)` + `simpleos_fat32_stream_read_at(0, buf,
size)` where `buf = simpleos_fat32_path_read_buffer_addr()`
(`examples/09_embedded/simple_os/arch/x86_64/fs_exec_general_ring3_entry.spl:58-76`). This C-backed
NVMe+FAT reader is **path-general** (not 8.3/registry) and **storage-mode-agnostic** (the harness proves
it over an NVMe namespace), and it writes the raw ELF into the same identity-mapped buffer the handoff
mmio-parses. Threading this into `_x86_64_read_spawn_bytes_and_blob` is the whole registry-free fix.

## 3. Ordered Edit Checklist

Anchors are current-file line numbers. Apply top-to-bottom; later steps assume earlier ones landed.

### (1) Raw-blob read seam — give every path a nonzero, identity-mapped blob

1. **`src/os/kernel/loader/x86_64_fs_exec_spawn.spl:12`** — beside the existing
   `extern fn simpleos_fat32_path_read_buffer_addr() -> u64`, add the two C stream externs the harness
   uses (currently declared only in the entry file):
   ```
   extern fn simpleos_fat32_stream_open(path: text) -> i64            # returns file size, or <=0
   extern fn simpleos_fat32_stream_read_at(file_off: u64, dst: u64, len: u64) -> i64
   extern fn rt_bytes_from_raw(ptr: i64, len: i64) -> [u8]            # pre-sized, no realloc
   ```
2. **`src/os/kernel/loader/x86_64_fs_exec_spawn.spl` (new fn above `:96`)** — add the generic seam,
   mirroring `fs_exec_general_ring3_entry.spl:58-76` and `vfs_init.spl:241-255`:
   ```
   fn _x86_64_read_generic_raw_exec(path: text) -> ([u8], u64):
       val fsize = simpleos_fat32_stream_open(path)          # path-general, no alias/registry
       if fsize <= 4: return ([], 0.to_u64())
       val buf = simpleos_fat32_path_read_buffer_addr()      # identity-mapped C buffer
       if buf == 0.to_u64(): return ([], 0.to_u64())
       val n = simpleos_fat32_stream_read_at(0.to_u64(), buf, fsize.to_u64())
       if n <= 0: return ([], 0.to_u64())
       # ELF magic guard against a stale buffer; ring3 re-guards magic+class+bounds too.
       if (mmio_read32(buf) as u64) != 0x464C457F.to_u64(): return ([], 0.to_u64())
       (rt_bytes_from_raw(buf as i64, fsize), buf)           # bytes AND blob from the SAME read
   ```
   Add `use os.kernel.boot.mmio.{mmio_read32}` if not already imported.
3. **`src/os/kernel/loader/x86_64_fs_exec_spawn.spl:96-107`** — rewrite
   `_x86_64_read_spawn_bytes_and_blob` so the **cache** and **generic** branches route through the new
   seam (they currently return `raw_blob=0` and fail closed). Minimal body:
   ```
   fn _x86_64_read_spawn_bytes_and_blob(path: text) -> ([u8], u64):
       _x86_64_read_generic_raw_exec(_x86_64_exec_canonical_path(path))
   ```
   Delete the now-dead `_x86_64_try_cached_exec` call (`:103-105`) — cache returned a zeroed blob and
   is the actively-harmful branch. (Alias/static branches are removed in step (4).)

### (2) Generic → real handoff routing — make the shell reach the arch loader

4. **`src/os/kernel/loader/fs_exec_spawn.spl` (new pub fn near `:240`)** — add an arch-dispatching entry
   so the shell reaches the ring-3 handoff without leaking arch logic into the shell:
   ```
   pub fn fs_exec_spawn_ring3(path: text, argv: [text], envp: [text]) -> i64:
       match _fs_exec_active_arch():
           Architecture.X86_64: x86_64_fs_exec_spawn(path, argv, envp)
           Architecture.Arm64:  arm64_fs_exec_spawn(path, argv, envp)
           _:                   fs_exec_spawn(path, argv, envp)   # legacy fallback for arches w/o ring3
   ```
   Add `use os.kernel.loader.x86_64_fs_exec_spawn.{x86_64_fs_exec_spawn}` and
   `use os.kernel.loader.arm64_fs_exec_spawn.{arm64_fs_exec_spawn}`.
5. **`src/os/apps/shell/exec.spl:9`** — change the import from `fs_exec_spawn` to `fs_exec_spawn_ring3`.
   **`src/os/apps/shell/exec.spl:40`** — change `val pid = fs_exec_spawn(resolved_path, argv, envp)` to
   `val pid = fs_exec_spawn_ring3(resolved_path, argv, envp)`. (PATH resolution at `:31`
   `shell_path_search` already returns an absolute path and does not depend on the registry — verified
   `path_search.spl:14,51-69` streams by path via `fs_exec_read_executable_bytes`.)

### (3) Retire the placeholder — fail-closed, never fabricate a pid

6. **`src/os/kernel/loader/x86_64_fs_exec_spawn.spl:127-128`** — delete the wine_hello shortcut
   (`if path == "/sys/apps/wine_hello" …: return _x86_64_spawn_static_seeded(...)`); let it fall through
   to the generic read.
7. **`src/os/kernel/loader/x86_64_fs_exec_spawn.spl:131-136`** — when `bytes.len() <= 4`, replace the
   `_x86_64_spawn_static_seeded` fallback with a fail-closed `return -2` plus the existing
   `spawn:resolve-fail` log.
8. **`src/os/kernel/loader/x86_64_fs_exec_spawn.spl:138-151`** — the SMF-stub extraction block: keep it
   for genuine `.SMF` envelopes, but on failure (`:142-147`) replace the `_x86_64_spawn_static_seeded`
   fallback with fail-closed `return -3`. (Pure ELF has no SMF trailer → `smf_has_header` false → this
   block is skipped anyway; the change only removes the fake-pid escape hatch.)
9. **`src/os/kernel/loader/x86_64_fs_exec_spawn.spl:43-58`** — delete `_x86_64_static_stub_size` and
   `_x86_64_spawn_static_seeded` entirely (now unreferenced). Verify no other `.spl` references them
   (`grep -rn _x86_64_spawn_static_seeded src/os`).

### (4) Registry-free path — remove allowlist/registry dependence from resolution

10. **`src/os/kernel/loader/x86_64_fs_exec_spawn.spl:16-41,60-95`** — after step (3), the alias resolvers
    `_x86_64_static_fat32_alias`, `_x86_64_try_static_fat32_exec`, and `_x86_64_try_fat32_exec_alias`
    are only reachable from the branches removed in step (1)/(3). Delete them (and drop the now-unused
    `g_vfs_read_fat32_path_bytes` import at `:3` if nothing else uses it). The generic seam already
    resolves any path. **Do not** delete `app_registry` globally — other subsystems use it; only remove
    exec's dependence on it.
11. **`src/os/kernel/loader/x86_64_fs_exec_spawn.spl:181` `x86_64_fs_exec_spawn_hello_world_smf`** —
    repoint the smoke wrapper at a fixed **path** (`/sys/apps/hellosmf.smf` or the baked ELF path) read
    through the generic seam instead of the deleted alias, so the existing smoke still builds. Keep it
    thin — it is only a build-time smoke, not part of the general path.

### (5) argv/env frame — real SysV AMD64 initial stack

12. **`src/os/kernel/loader/x86_64_fs_exec_ring3.spl:224-236`** — the stack loop currently discards each
    page's phys addr `sph` and sets `user_rsp = STACK_TOP-16` with **no frame**. Capture the 32 phys
    pages into a fixed array during the map loop:
    ```
    var stk_phys: [u64] = []      # index 0 = page at [STACK_TOP-PAGE, STACK_TOP)
    … push sph after each successful vmm_map_page_in …
    ```
13. **`src/os/kernel/loader/x86_64_fs_exec_ring3.spl` (new fn)** — add
    `_build_sysv_stack_frame(stk_phys, STACK_TOP, argv, envp) -> i64` that writes, via `mmio_write8`/a
    `_wr64` helper, into the user stack by translating a user vaddr in `[STACK_TOP-32*PAGE, STACK_TOP)`
    to its phys page (`stk_phys[(STACK_TOP-1-vaddr)/PAGE]`) and offset. Frame layout (SysV AMD64, low→high
    from the returned rsp; `_start` reads these off the stack — do **not** pass them in registers):
    ```
    [rsp]              argc                       (i64)
    [rsp+8 ..]         argv[0..argc-1] pointers
                       0                          (argv NULL terminator)
                       envp[0..] pointers
                       0                          (envp NULL terminator)
                       auxv: AT_NULL(0), 0        (minimum viable auxv terminator)
    (higher)           NUL-terminated string data for argv/envp
    ```
    Lay strings at the top of the window first, record their user-vaddrs, then lay the vector below them.
    **Align:** choose the vector base so the final `rsp % 16 == 0` with `[rsp]=argc` (pad one 8-byte slot
    if the slot count is odd — same rule as Linux `create_elf_tables`). Return that `rsp`.
14. **`src/os/kernel/loader/x86_64_fs_exec_ring3.spl:236,239-249`** — set
    `user_rsp = _build_sysv_stack_frame(...)` and keep `rdi=rsi=rdx=0` in the `TaskContext` (ABI: at
    `_start` the arg registers are undefined except `rdx`=atexit fn, which 0 satisfies). `cs=0x2b`,
    `ss=0x23`, `rflags=0x3002` unchanged. Thread `argv,envp` into
    `x86_64_fs_exec_enter_image_ring3(image, blob, argv, envp)` (add the two params; caller
    `x86_64_fs_exec_spawn.spl:168` already has them). Gate: if `argv.len()==0`, write the minimal
    `argc=1, argv[0]=binary_path, NULL, NULL, AT_NULL` frame so even argv-ignoring payloads get a valid
    frame and `rsp` stays 16-aligned (the current verification payload keeps passing).

### (6) ARM parity (noted)

15. **`src/os/kernel/loader/arm64_fs_exec_spawn.spl:7` `arm64_fs_exec_spawn`** — mirror the seam: add the
    same generic raw-blob read (steps 1-3) and route into an AArch64 ring-3 handoff. **Blocker to note:**
    there is no `aarch64_fs_exec_ring3.spl` today (only `x86_64_fs_exec_ring3.spl` exists). Land the
    AArch64 handoff as a follow-on that reuses the same `create_user_address_space` + `_map_pt_loads`
    (arch-neutral, MMIO-parsed) and differs only in EL0 entry: set `SPSR_EL1` (EL0t, IRQ/FIQ per policy),
    `SP_EL0 = user_rsp`, `ELR_EL1 = entry`, `eret`. The SysV/AAPCS64 initial stack frame layout (step 5)
    is **identical** (argc/argv/envp/auxv on the stack); only the entry sequence changes. Until the EL0
    handoff exists, `fs_exec_spawn_ring3` (step 4) leaves Arm64 on the legacy fallback — x86_64 ships
    first, ARM parity tracked as the immediate next task.

### (7) Verification harness + command + markers

16. **`scripts/os/build_fsexec_general_ring3.shs`** — add a **shell-driven, PATH-based, registry-free**
    variant (or a sibling `build_fsexec_shell_pathexec.shs`) whose `--entry` boots to a shell,
    places an arbitrary ELF at a **non-registered** path (e.g. `/usr/bin/probe.elf`, NOT in
    `_x86_64_static_fat32_alias` nor `app_registry`), then runs `shell_exec("probe.elf", …)`. Reuse the
    q35 + `fat32-fsexec.img` NVMe-namespace boot, `-device isa-debug-exit,iobase=0xf4`, and the serial
    grep block (`:89-91`). The new entry must call `fs_exec_spawn_ring3` (step 4), not the neutral
    `fs_exec_spawn`, so the path exercises the real handoff.
17. **New entry** `examples/09_embedded/simple_os/arch/x86_64/fs_exec_shell_pathexec_entry.spl` — clone
    `fs_exec_general_ring3_entry.spl:78+` but replace the direct
    `x86_64_fs_exec_enter_image_ring3(image, buf)` call with `shell_exec("probe.elf", [], [])` after
    seeding PATH, proving the **full shell → PATH → generic-read → handoff → CPL3** chain.

## 4. Risks (guest fault/hang) + Mitigations

| # | Failure mode | Where | Mitigation |
|---|---|---|---|
| R1 | `raw_blob=0` on a general path → fail-closed rc=-5, no CPL3 | seam step 1-3 | Generic stream read always returns the identity-mapped `buf`; ELF-magic guard in the seam and re-guard at `ring3.spl:185-190` catch a stale buffer. |
| R2 | Blob ≠ the bytes just read (stale buffer holds a different resident ELF) → mmio-parses wrong ELF, maps wrong segments | seam step 2 | `bytes` **and** `blob` come from the **same** `stream_read_at` into `buf`; magic guard rejects a clobbered buffer. Never return `simpleos_fat32_path_read_buffer_addr()` without a preceding read that filled it. |
| R3 | Boxed-`[u8]` header read → `magic≈248, phoff=16` → phdr OOB or bogus entry → `#PF` on `iretq` | ring3 parse | Handoff parses via `mmio_read*` off the raw buffer only (`ring3.spl:54-55,178-193`); never off `image.file_bytes`. |
| R4 | phdr table / segment file-range OOB drives mmio past the buffer | `_map_pt_loads` | Existing bounds `ring3.spl:78-92` (`ph_table_end > file_len`, `foff+fsz > file_len`) reject it → rc=-2 fail-closed, no partial map. `file_len` = `fb.len()` from the same read. |
| R5 | Stack top in an unpopulated PML4 subtree → first push `#PF` | ring3 stack | Keep `STACK_TOP=0x8000200000` (PML4[1], shared with the code mapping via `vmm_clone_kernel_low_identity`); 32-page window at `0x80001E0000` stays clear of the code page at `0x8000000000` (`ring3.spl:213-236`). |
| R6 | Misaligned `rsp` or malformed SysV frame → glibc/Rust `_start` faults reading `argc`/`auxv` | argv frame step 5 | Build a real `argc/argv/envp/AT_NULL` frame; enforce `rsp % 16 == 0` with `[rsp]=argc` (Linux `create_elf_tables` rule); minimal `argc=1` frame when argv empty so argv-ignoring payloads still get a valid, aligned stack. |
| R7 | Non-static / dynamically-linked / PIE ELF (needs interpreter or relocation) → entry faults | general ELF | v1 scope = static ELF (harness payload, `hello_rs`). Detect `PT_INTERP`/`ET_DYN` in `_map_pt_loads` and fail-closed with a clear log (`FAIL needs-interp`) rather than mapping and faulting; dynamic loading is a tracked follow-on, not this plan. |
| R8 | Retiring the placeholder breaks the existing SMF smoke build | step 3/4 | Repoint `x86_64_fs_exec_spawn_hello_world_smf` (`:181`) at a real path through the generic seam (step 11); run the existing smoke in CI before/after. |
| R9 | Pure-Simple NVMe storage mode has no C `simpleos_fat32_read_path` buffer | seam | The seam uses `simpleos_fat32_stream_open`/`stream_read_at` (C NVMe+FAT reader), which the harness proves works over the NVMe namespace **independent** of `vfs_boot_storage_is_pure_simple()`; it writes the identity-mapped buffer directly. If a target lacks the C stream reader, fail-closed (rc<0), never map garbage. |
| R10 | TSS/GDT not set for CPL3 → `#GP`/`#TS` on `iretq` | entry | `rt_x86_tss_init()` is already called in the harness entry before the handoff; the shell-path entry must call it too (step 17). Ring0→ring3 GDT selectors `cs=0x2b/ss=0x23` already proven. |
| R11 | ARM path silently uses legacy phantom-pid fallback | step 4/6 | `fs_exec_spawn_ring3` routes Arm64 to `arm64_fs_exec_spawn`; until the EL0 handoff exists it must fail-closed on a real ELF (not return a phantom pid), with a `arm64:no-ring3-handoff` log. |

## 5. Verification Command(s) + Pass/Fail Markers

**x86_64 shell-driven, registry-free (primary proof):**
```bash
scripts/os/build_fsexec_shell_pathexec.shs        # new (step 16); or the extended general script
```
**x86_64 direct-handoff regression (existing, must stay green):**
```bash
scripts/os/build_fsexec_general_ring3.shs
```

Both native-build a kernel, boot QEMU q35 with `fat32-fsexec.img` as an NVMe namespace, and
self-terminate via `syscall 60` + `out 0xf4` (QEMU_TIMEOUT default 40s).

**PASS** (all three, in order, from an ELF at a non-registered PATH entry):
- `[spawn] image path=… entry=0x… segments=N` — real image built + handoff entered (N = real PT_LOAD count, not the fake `segments=1`).
- `FDR` — ring-3 `out` succeeded (only reachable at CPL3; definitive ring-3 proof).
- `FSEXEC_OK rc=42` — payload ran to completion and self-reported via `syscall 60`.

**FAIL** (any of):
- `[spawn] FAIL raw blob address is 0` / `handoff-return … rc=-5` — seam still returns `raw_blob=0` (steps 1-3 incomplete).
- `[spawn] FAIL blob not ELF` / `FAIL not ELFCLASS64` — stale/wrong buffer (R2) or bad file.
- `[spawn] FAIL phdr table OOB` / `FAIL segment file range OOB` — bounds tripped (R4).
- Any `entry=0 segments=1 stub_bytes=…` line — the retired placeholder is still live (step 3 incomplete).
- No `FDR` within timeout — `#PF`/`#GP` before/at CPL3 (R5/R6/R10) or a hang; inspect the last `[spawn]` line.
