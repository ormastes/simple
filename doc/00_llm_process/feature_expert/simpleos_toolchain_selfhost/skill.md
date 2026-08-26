# SimpleOS Toolchain Self-Host (clang + Simple migration) Feature Expert

> **Restart12 authority (2026-08-14):** the artifact/DONE table below is
> historical unless a current receipt revalidates it. The canonical current
> plan is `doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`;
> Stage 2 is bootstrap-only, while Stage 3/4, payload, guest-static lld, image,
> SSpec execution and live receipts remain BLOCKED/WARN. The combined wrapper's
> canonical Stage-4 admission, preflight, and shared receipt contract are
> source-complete and self-tested; live mode correctly blocks on the missing
> canonical same-run desktop/SSHD hook.
> The current x86_64 compiler repair keeps local `HirType` aggregates inside
> their owning MIR metadata arrays and copies them by scalar local IDs. Its
> focused native regression is green; Stage 3/4 admission is still pending.
> The canonical SSpec surface now distinguishes source contracts, host-wrapper
> fixtures, image-admission checks, and the sole live deployment/desktop scenario.
> Source inventories, compatibility duplicates, and Rust-seed presence are not
> guest or release evidence.
> The live umbrella SSpec additionally exposes step-based positive receipt,
> extra-argument edge, and missing-runtime error coverage with real assertions.
> Runtime/docgen/maintenance status is `TEST_BLOCKED` until a current-source
> CLI passes canonical Stage-4 provenance admission; the mirrored manual is not
> runtime evidence.

## Role

Own feature-specific process knowledge for the **clang + Simple migration onto
SimpleOS**: building an `x86_64-unknown-simpleos` LLVM/clang/lld cross toolchain
whose outputs are *guest-runnable*, porting the real Simple runtime so the
Simple payload links for SimpleOS, and driving the OVMF-pflash ladder from
in-guest COMPILE through in-guest LINK+RUN — fixing each SimpleOS defect at its
owner layer rather than masking it.

Campaign lane: `.spipe/simpleos_clang_simple_migration/state.md` (10 ACs).
Plan of record: `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`
(+ `_tldr`).

## Status as of 2026-08-06 — read this before claiming anything

| AC | Claim | State |
|---|---|---|
| AC-1 | Fork holds all SimpleOS work; `build.spl` pin == fork tip | **DONE** — both `596122063`, verified by `git ls-remote` |
| AC-2 | Cross clang/lld build **guest-runnable** | **DONE** — `bin/clang-20` 127,572,072 B; `bin/lld` 64,526,504 B; both Type=EXEC, entry `0x40000000`, **0 INTERP** |
| AC-3 | `bin/release/x86_64-unknown-simpleos/simple` links | **DONE (STAGING)** — 2,300,776 B, ET_EXEC, entry `0x40000000`, 0 INTERP, **0 undefined `rt_*`** |
| AC-4 | In-guest clang compile → **byte-exact** object under real firmware | **COMPILE PROVEN 2026-08-06 — AC NOT FULLY MET.** Byte-exactness is unproven: L5 host-side `getfile` retrieval returns an empty object, so nothing was compared. Do not report AC-4 as DONE. |
| AC-5 | In-guest LINK + RUN (`ld.lld` in guest, FS-exec the result) | **NOT DONE** — rungs 3–6 of `scripts/os/ssh_lld_link_uefi.shs` have never executed |
| AC-6 | Install-image seven paths + live `ssh root@guest /usr/bin/simple /hello.spl` rc=0 | **NOT DONE** |
| AC-7 | Simple `--emit-object` → in-guest link → run | **NOT DONE** |
| AC-8 | Clang self-compile witness (one real LLVM TU, byte-compared) | **NOT DONE** |
| AC-9 | Every defect fixed at its owner layer, no fabricated stubs | ongoing |
| AC-10 | Board-runnable status stated honestly | blockers filed and visible |

**Two honesty constraints that must survive every rewrite of this page:**

1. **AC-3 is STAGING, not self-hosted.** The payload was built by the *Rust
   bootstrap seed* (`SIMPLE_BUILD_COMPILER=src/compiler_rust/target/bootstrap/simple`,
   seed sha256 `13ebe5dd22f0cabf…`) as the **D1** route-around, because the
   deployed self-hosted `bin/release/simple` SEGVs on `native-build`. The
   payload is **linked, not run**. Do not upgrade this to a self-host claim.
2. **The physical board is NOT reached.** Every gate is the x86_64 OVMF-pflash
   real-firmware proxy (never `-kernel`, never `isa-debug-exit`). Board
   blockers stay filed: mini-PC not purchased (P0.3) and no physical NIC driver
   (virtio-net only). `.claude/rules/board-runnable.md` applies.

### AC-4 evidence (the exact markers — quote these, don't paraphrase)

```
  [ok]   L1 OVMF -> GRUB-EFI app ran
  [ok]   L2 multiboot handoff -> kernel _start
  [ok]   L3 sshd ring-3 accept loop (payload overlap fault cleared)
  [ok]   L4 in-guest clang compiled /hello.o under OVMF
[VMM] portable VMM published kernel PML4 0x402718720
[oo-nvme] persist /hello.o -> OK      [syscall] exit status=0
```

`build/os/vmm_gate_run.log` + `build/os/scp_retrieve_over_ssh_uefi.serial.log`,
2026-08-06 05:48, KVM-accelerated, OVMF pflash. Clang ran as an FS-exec **ring-3**
process. Stub ratchet on that run: 56 known, 0 new.

**Precise scope of AC-4:** the in-guest *compile* is proven. **Byte-exactness of
the object is NOT** — **L5 (host-side `getfile` retrieval) still returns an empty
object**, so nothing has been compared against the host cross build. That is a
retrieval-transport gap, not a ring-3 defect; don't read L5 as an AC-4
regression, but don't claim byte-exact either.

## Pipeline Links

## 32-bit receipt boundary (2026-08-21)

Use `src/os/port/simpleos_32bit_bootstrap_contract.spl` for x86_32, ARM32,
and RV32 target metadata and receipt admission. The v2 validator binds Phase
1/2 lineage, sysroot/linker/tool manifests, QEMU identity, exit 37, and four
nonce-bearing transcript markers. Offline specs never prove a live or
target-native bootstrap; resume rows are Todo 834-836.

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Plan of record:
  [doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md](../../../03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md)
  (§0 "Ground truth" is a *do not re-derive* table; §1 has the lane dependency graph).
- TL;DR: `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan_tldr.md`
- Campaign state / ACs: `.spipe/simpleos_clang_simple_migration/state.md`
- Guide — **partially stale in BOTH directions, see trap 8 before trusting it**:
  [doc/07_guide/os/simpleos_llvm_toolchain.md](../../../07_guide/os/simpleos_llvm_toolchain.md)
  (lane C2 removed its false "prebuilt artifacts exist" claims; but its
  build-status table was written pre-C1 and now under-reports — it still says the
  cross stage is NOT BUILT, contradicted by the 127 MB `clang-20` on disk.)
- Link ladder: `doc/03_plan/os/in_guest_lld_link_ladder.md`,
  `doc/03_plan/os/in_guest_clang_selfhost_board_plan.md`
- Freestanding codegen landmines (**D3**, applies to every guest-run `.spl`):
  `doc/07_guide/os/baremetal_simple_codegen_landmines.md`

## Affected Layers

- [layer_expert/os_kernel_exec](../../layer_expert/os_kernel_exec/skill.md) —
  VMM/PML4 publication, FS-exec ring-3 loader, FAT32, libc/crt0, image builder.
- [layer_expert/llvm_toolchain_port](../../layer_expert/llvm_toolchain_port/skill.md) —
  the LLVM fork, cross CMake toolchain file, sysroot, `clang_static.shs`.
- [layer_expert/bootstrap](../../layer_expert/bootstrap/skill.md) — the seed vs
  self-hosted builder distinction that makes AC-3 staging-only.

## Load-Bearing Facts

1. **The guest-runnable enabler is two flags, not a relink.**
   `-static` **plus** `-Wl,-T,<sysroot>/share/simpleos/simpleos.ld` in
   `src/os/toolchain/llvm/simpleos_cross_toolchain.cmake`. Without them the host
   clang driver **defers the link to gcc** and emits a Linux-dynamic ELF with an
   INTERP segment that the FS-exec loader cannot run. This is exactly why the
   **DEPRECATED** `src/os/port/llvm/clang_static.shs` static-relink existed; it
   is no longer needed for a guest-runnable image. If you find yourself reaching
   for it, first check whether the cmake flags were dropped.
2. **The Simple payload links because the REAL runtime was ported, not shimmed.**
   17 of the 20 missing `rt_*` symbols came from `src/runtime/runtime_native.c`
   (including the whole transient-heap protocol); 3 (`rt_pop`, `rt_clear`,
   `rt_env_remove`) existed only in Rust
   (`src/compiler_rust/runtime/src/value/collections.rs`) and were written
   *inside* `runtime_native.c` against the verified `RtCoreArray` layout; 1 was a
   libc gap. The result is `src/os/port/llvm/sysroot.shs` building
   `libsimple_runtime_native.a` from **8 objects, one `.o` per source, never
   `ld -r`** (archive-member granularity is the layering enforcement mechanism —
   see trap 3).
   - The cheap alternative — "just trim the import closure" — was **tested and
     REFUTED**: reverting the only changed import edge in
     `src/app/simpleos_tool/main.spl` gave a **byte-for-byte identical** failure
     (`511 unexpected symbol(s)`). 5 of the undefined refs are demanded by
     `libsimple_runtime.a` *itself*, so no payload edit could ever remove them.
     `--runtime-bundle core-c-bootstrap` also produced the identical 20 symbols,
     killing that hypothesis too.
   - **`struct SplArray` in `runtime.h:126` is a DECOY.** The real layout is
     `RtCoreArray { kind; flags; reserved; transient_scope_id; len; cap; data }`.
     And **`rt_clear` is NOT an alias for `rt_array_clear`** — `rt_array_clear`
     returns `1`, which decodes as `RT_VALUE_TAG_HEAP | 0`, i.e. a NULL heap
     pointer.
   - Why the merge is an `ar r` and not a fourth link input: the seed linker
     hardcodes exactly three inputs (`crt0.o`, `lib/libsimple_runtime.a`,
     `lib/libsimpleos_c.a`) at
     `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:207`.
     There is no fourth slot.
   - Accepted, documented limitations (not stubs): `fsync`/`fdatasync` return
     `-1`/`ENOSYS` (blast radius verified zero); `pread`/`pwrite` are seek-based
     (only syscalls 31 Read / 32 Write / 46 Lseek exist); `getaddrinfo` handles
     numeric + `AI_PASSIVE` only, else `EAI_NONAME`.
   - Fabricated `rt_*` stubs are forbidden by AC-9.
3. **LLVM fork:** `github.com/ormastes/llvm-project`, branch `simpleos`
   (Clang 20), local checkout `/home/ormastes/llvm-project`. Pinned by
   `LLVM_REVISION` in `src/os/port/llvm/build.spl`. Pin drift is a real, recurring
   failure — verify with `git ls-remote`, not with the local checkout.
4. **The D6 blocker was two parallel VMM implementations.** Both printed
   **byte-identical `[VMM]` banners**. The live init
   (`src/os/kernel/arch/x86_64/paging.spl:214`) wrote its own struct, while every
   consumer read `vmm_core`'s global — which was never written, because
   `vmm_core`'s own `vmm_init` **has zero callers (dead code)**. Result:
   `vmm_kernel_pml4_phys()` read 0 after a demonstrably successful init, so
   `create_user_address_space` fell back to the legacy sentinel and **every**
   FS-exec ring-3 spawn returned `rc=-1`. Fixed by `vmm_publish_kernel_pml4()`
   (+35 lines, 2 files), commit `4575b4ce88d`. Ruled out first, with evidence:
   a single `_vmm_pml4_phys` symbol (no duplicate `.bss`) and a real accessor body.
5. **Guest FS is FAT32 root-directory-only, 8.3 names** (LFN parsed; subdir
   *read* traversal landed in lane B2, 17/17 spec, sabotage-verified). Stage
   everything as `HELLO.O` / `LLD.ELF` / `LIBC.A` in the root.
6. **fork is UNREACHABLE, not broken.** Fork(57)/Exec(59) are fully implemented
   (`src/os/kernel/ipc/syscall_process.spl:237` `_handle_fork`, `:252`
   `_handle_exec`) yet unreachable for **two independent** reasons: (a)
   `x86_64_fs_exec_ring3.spl:311` hand-builds the address space and `iretq`s
   without `create_task`/`register_task_vmspace`, so `sched.get_current()` has no
   task to clone; and (b) `_bare_exec_mode = 1` makes `rt_syscall_dispatch` offer
   every syscall to `_bare_exec_handle` FIRST, whose switch covers
   `0, 4, 10, 11, 12, 15, 30–34, 39, 43, 44, 46, 47, 50, 60, 69` — **no 57, no
   59**. Fixing one reason alone changes nothing. What landed instead is
   **SpawnWait as syscall 120** (deliberately not 57/59; and not 70, which is
   already `net_socket` and produced a duplicate `case` label), handler in
   `src/os/kernel/loader/x86_64_fs_exec_spawn.spl`, plus a resume *stack*
   (`RING3_RESUME_MAX_DEPTH = 4`) replacing the single-slot savepoint. **cr3-restore
   correctness is reasoning-only, unverified.** This is why AC-5 invokes `ld.lld`
   as a **direct absolute-path FS-exec**, never through the clang driver.
7. **Memory layout is load-bearing:** kernel links at 128 MB
   (`linker_128mb.ld`), `.bss` `[0x08000000, ~0x16400000)`; ring-3 link
   `0x40000000`; mmap `0x50000000`. Clang lanes need `QEMU_MEM=2G` or more.
8. **Scope exclusions are deliberate, not oversights:** aarch64 (filed EFI-stub /
   PE-header gap + seed arm64 miscompile), riscv64 clang hosting (the on-hand ML
   Carrier board has 64 MiB RAM; the clang payload alone is ~124 MB), and full
   in-guest clang self-BUILD (B4 — needs FAT32 write/subdirs, fork/exec, ≥8 GB
   RAM / ~20 GB disk). AC-8 is the honest scoped witness instead of B4.

## Traps — each with its discriminating check

These are the ones that actually cost time on 2026-08-06. Every entry pairs the
misleading signal with the check that separates it from the real cause.

1. **A CMake `check_*_compiles` FATAL_ERROR names the PROBE, not the cause.**
   Real example: CMake reported `libstdc++ version must be at least 7.4.`
   (`CheckCompilerVersion.cmake:88`) and `Host compiler appears to require
   libatomic` (`CheckAtomic.cmake:59`). **Both were false.** The actual
   diagnostic existed only in the configure log:
   `ld.lld: error: undefined symbol: rt_array_len`.
   → **Check:** read `CMakeFiles/CMakeConfigureLog.yaml` in the build directory
   for the probe's real compiler/linker invocation and its diagnostics, then
   replay that exact link by hand. Never debug from the FATAL_ERROR line.
2. **Derived archive copies silently reproduce an already-fixed error.**
   `build/os/sysroot/lib/libm.a` is a **`cp` of `libsimpleos_c.a`**
   (`src/os/port/llvm/sysroot.shs:266`), and `-lm` precedes
   `-Wl,--start-group -lc++ -lsimpleos_c -lm` on the link line — so a stale
   `libm.a` (dated 2026-07-30) kept failing the identical link *after* the real
   fix landed, making a correct fix look like no fix.
   → **Check:** when a fix "doesn't take", look for derived copies first —
   `cmp build/os/sysroot/lib/libm.a build/os/sysroot/lib/libsimpleos_c.a` and
   compare mtimes — then regenerate. Related **concurrency hazard:** the cross
   build links against `build/os/sysroot/lib/` while `sysroot.shs` rewrites
   `libm.a`; never regenerate the sysroot while a cross build is linking. Stage
   to a scratch sysroot and swap.
3. **Archive members link per-OBJECT, so a bridge sharing a TU with core libc
   makes its dependency mandatory.** `src/os/libc/simpleos_libc.c` held the
   Simple-runtime CLI-argv bridge (`rt_set_args`, `rt_cli_arg_*`, `spl_init_args`,
   …) in the same translation unit as core libc, so *every* C/C++ link pulled the
   core object and with it undefined `rt_array_new`/`rt_array_push`/
   `rt_array_len`/`rt_string_new`. Splitting the TU is the fix; hiding the
   symbol is not.
   → **Check:** `nm -u` **per member**, not per archive —
   `nm -u simpleos_libc.o | grep -E 'rt_array|rt_string'` → none, while
   `nm -u simpleos_cli_args.o | grep -cE 'rt_array|rt_string'` → `4`. That is
   what localises the offending object. Fix landed as a new TU
   `src/os/libc/simpleos_cli_args.c`. **Rule: one `.o` per source, never
   `ld -r`** — archive-member granularity is the layering enforcement mechanism.
   → **Sibling in the same family:** `environ` was defined twice —
   `.globl environ` in `simpleos_crt0.S` (8 B `.bss`) vs
   `char **environ = _env_storage;` at `simpleos_process.c:26` (`.data`) — and
   `crt0.o` is on every link line, so the clash was unconditional
   (`ld.lld: error: duplicate symbol: environ`). Fixed by `.globl` → `.weak`
   (`nm simpleos_crt0.o | grep environ` → `W environ`). Note the history: the
   crt0 definition was itself the fix for the **opposite** bug — a weak ref with
   no definition resolved to 0 and `mov [environ], r14` faulted at `_start`
   (ring-3 #PF, errcode `P|W|U`, `cr2=0`). **Defensive definitions for
   possibly-missing symbols must be `.weak`, never `.globl`.**
   → **Third member of this family, filed OPEN but apparently already fixed in
   the working tree — re-check before acting.** `struct __simpleos_FILE` was
   defined twice with incompatible layouts: `simpleos_libc.c:362` `{ int fd; }`
   (**4 B**) vs `simpleos_fs.c:116`
   `{ int fd; int eof; int error; int mode; }` (**16 B**). `FILE` is opaque in
   `include/stdio.h`, so no TU sees the other and the compiler **cannot**
   diagnose it; `fread`/`fwrite`/`fclose` write up to 12 bytes past the 4-byte
   `_stdin_f`/`_stdout_f`/`_stderr_f` statics, and `fclose(stdout)` would
   `free()` a non-heap pointer. As of 2026-08-06 the prescribed fix appears
   applied — a single definition now lives in the (untracked)
   `src/os/libc/simpleos_file_internal.h` and both local copies are gone — while
   the bug doc still reads OPEN.
   → **Check (also the cheap durable regression guard):**
   `grep -c 'struct __simpleos_FILE {' src/os/libc/*.c src/os/libc/*.h` — the
   total must be exactly 1, and it must be in the header. Confirm and close the
   bug doc rather than re-deriving the defect.
4. **A log marker that does not identify its WRITER cannot distinguish two
   implementations.** Two VMM paths printed **byte-identical `[VMM]` banners**,
   so a green-looking log proved nothing about which struct was live (this is
   D6, and it gated AC-4 through AC-8).
   → **Check:** confirm the *consumer* reads the same global the *writer* wrote,
   and grep for callers of the initializer — `vmm_core`'s `vmm_init`
   (`vmm_core.spl:273`/`:282`) had **zero callers**, i.e. dead code posing as the
   live path, while `arch/x86_64/paging.spl:214` was the real initializer. Two
   plausible hypotheses were correctly ruled out *with evidence* first:
   `nm` found exactly ONE `_vmm_pml4_phys` (no duplicate `.bss`), and `objdump`
   showed a real accessor body (`mov $0x80c4138,%rdi; mov (%rdi),%rax; ret`), not
   a stub. Failure markers to recognise:
   `[VMM] create_user_address_space: VMM not initialized — legacy AS=1`,
   `[spawn] FAIL user-AS synthetic root=1`, `rc=-1`. Fix
   (`vmm_publish_kernel_pml4`) sets **scalars only**, because `g_vmm` is a struct
   global with a constructor initializer — an unreliable freestanding category
   (**D3**).
5. **The fabricated-stub guard FAILS OPEN for an entry with no baseline rows.**
   `config/freestanding_fabricated_stub_baseline.sdn` has **zero rows** for
   `simpleos_ssh_ring3_uefi128.elf`, and `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:299-314` only **WARNS** for an
   unbaselined entry (it hard-fails on new fabrications only once baselined).
   Under `SIMPLE_ALLOW_FREESTANDING_STUBS=1` this channel fabricates weak no-op
   bodies when a source file fails to build, yielding a **green build with dead
   code**. It really happened: prose inserted after the closing `*/` in
   `enter_user_first.s` stopped it assembling, and the build stayed green with a
   **no-op `iretq`**.
   → **Check:** accept a kernel fix only on a **POSITIVE** marker — for D6 that
   is `[oo-nvme] persist /hello.o -> OK`. **Never accept an ABSENCE condition**
   ("the failure line is gone") as proof: a stubbed accessor satisfies every
   absence condition. Additionally: `nm` the ELF and require `T`, not `W` —
   `rt_x86_enter_user_first` reading `W` (with `_ring3_resume_buf` absent
   entirely) was the tell, alongside the log line
   `FABRICATED-NEW spawn_wait_ring3.elf rt_x86_enter_user_first`. For an assembly
   file, **assemble it standalone**: `clang --target=x86_64-unknown-elf -c`.
   Diff the `FABRICATED-NEW` symbol set before vs after any kernel change, and
   baseline the entry on a known-good PRE-fix build to turn the channel into a
   ratchet.
6. **`file` says "dynamically linked" for a `--export-dynamic` static binary.**
   Reading `file(1)` output supports a false "the toolchain still emits dynamic
   ELFs" conclusion.
   → **Check:** `readelf -l <bin> | grep -c INTERP` must be **0**, plus
   `readelf -h` showing `Type: EXEC` and `Entry point address: 0x40000000`.
   That triple is the guest-runnable contract; `file` is not evidence.
7. **Image-builder provenance was asymmetric — and the WEAKER guard ran first.**
   The shell `validate_simple_payload_provenance()`
   (`scripts/os/make_os_disk.shs:52`) checks stamp freshness, `target=`,
   `entry=`, `entry_closure=`, `backend` ∈ {llvm, cranelift} and rejects a
   `compiler` matching `*compiler_rust*`/`*simple_seed*`. The Simple
   `_validate_simple_binary()` (`src/os/installer/image_builder.spl:886`, called
   at `:218`) checked only `target=`/`entry=`/`entry_closure=` + ELF
   magic/class/machine — **nothing about `compiler=`, `backend=`, or freshness**.
   Because it ran first, **12 seed-built role files were staged into the rootfs**
   before the shell layer refused. The refusal message
   (`invalid SimpleOS Simple payload build stamp compiler: …` /
   `Error: FAT32 disk generation failed; refusing non-bootable descriptor
   fallback`) is the guard **working**; the defect was the staging that preceded
   it. Per the plan, host `bin/simple` and marker apps are **NOT** pass evidence
   for AC-6.
   → **Check:** assert the seven install paths *and* the payload's SHA-256
   against the S1 artifact, not merely that the paths exist. Side finding worth
   knowing: staged `.smf` files are bare ELF with **no** 128-byte `SMF` trailer
   (`make_os_disk.c:460` appends it), so SMF-envelope claims need their own
   evidence.
8. **A stale guide is an active hazard, not cosmetic.** The toolchain guide
   claimed prebuilt cross clang-20/lld existed ("already built, just not on the
   `PATH`", 131 MB `clang-20`) while the filesystem had only `CMakeCache.txt` —
   **no `bin/`, no `build.ninja`**. Corrected in lane C2, and the drift itself is
   filed as a bug so the class stays visible.
   → **Check:** verify artifact claims against the filesystem, not the prose —
   `find build/os/llvm -maxdepth 3 -name build.ninja -o -maxdepth 3 -name bin`.
   A commit-pinned historical proof (`7cf0b6aec3a` for `-cc1`, `fe9fbd8c2285` for
   the interpreter hello) does **not** satisfy a fresh lane. **"FIXED" on that
   bug means the document matches the filesystem, not that the toolchain
   exists** — and since C1 landed, parts of the guide's build-status table have
   drifted the *other* way (it still says cross NOT BUILT). Re-check both
   directions.
9. **`s[i] as u8` on `text` silently yields ZERO under `bin/simple run`.**
   Encountered while hand-building a FAT32 image: it produced a plausible-looking
   boot sector (`BPS=0200 SPC=01 reserved=20 FATs=02 root_cluster=02`) with an
   **all-NUL** OEM field and dirent name. A structurally valid artifact is not a
   correct one.
   → **Check:** assert on byte *content* of generated binary structures, never
   only on their parseability.

## Bug Records (read these before re-deriving)

All in `doc/08_tracking/bug/`, all dated `2026-08-06`:

| Bug doc (`…_2026-08-06.md`) | Status | Encoded as |
|---|---|---|
| `simpleos_libc_leaks_simple_runtime_syms` | FIXED | traps 1, 2, 3 |
| `simpleos_crt0_environ_duplicate_symbol` | FIXED | trap 3 |
| `simpleos_libc_file_struct_odr_mismatch` | doc says **OPEN**; fix appears applied in-tree — verify & close | trap 3 |
| `simpleos_vmm_kernel_pml4_phys_reads_zero_after_init` | FIXED (D6) | traps 4, 5 |
| `simpleos_payload_link_missing_20_rt_symbols` | FIXED | fact 2 |
| `simpleos_image_builder_provenance_asymmetry` | FIXED | trap 7 |
| `simpleos_llvm_toolchain_guide_claimed_prebuilt_artifacts` | FIXED (D4) | trap 8 |
| `fs_exec_ring3_fork_unreachable_spawnwait` | impl landed, **in-guest proof not obtained** | fact 6, trap 5 |
| `b1_witness_guest_clang_heap_exhausts_on_real_tu` | RESOLVED — SIGABRT root-caused (`operator new(0)` returned NULL: guest `malloc(0)` legally returns NULL but `_Znwm`/`_Znam` in `simpleos_cxxabi.c` didn't special-case size 0, violating C++'s never-null-for-size-0 `operator new` guarantee, `13abfa0ca2f`) and fixed; `-cc1` now compiles the real TU to completion in-guest. The post-fix `.text` divergence from the host reference was **root-caused as a wrong-compiler reference, not a guest bug** (`5e80b53c5d1`): the host-repro control used stock Ubuntu clang-20.1.8, not this project's LLVM fork (20.0.0git @ `59612206386553df`) that the guest actually runs. The entire `.text` diff is one functionally-equivalent instruction-selection choice (`tzcnt` vs `bsf`+`cmovne` for `countTrailingZeros`); every other differing byte is the same downstream +3-byte address shift. Both codegens are correct. | new trap below |
| `simpleos_userspace_crt0_missing_module_init_call_empty_init_array` | FIXED (x86_64 `3525e837a0e`, aarch64 `1e9311483f7`) | new entry below |

**New trap:** after editing any `src/os/libc/*.c` file, the B1/B-lane
harnesses (`SKIP_KERNEL=0`, `SKIP_STAGE=1`) rebuild the **kernel** and
re-copy the FAT32 payload but never rebuild `build/os/clang_static/bin/clang_static`
itself — it silently keeps running the OLD, pre-edit `libsimpleos_c.a`. Must
manually: `cd src/os/libc && make` → `cp libsimpleos_c.a
../../../build/os/sysroot/lib/libsimpleos_c.a` → `sh
src/os/port/llvm/clang_static.shs` before rerunning. Verify with `strings
build/os/clang_static/bin/clang_static | grep -c <new-diagnostic-string>`
before trusting a "no crash" or "message never fired" result out of a B1
rerun — a null result from a stale binary reads identically to a real one.

Plus the standing gate defects **D1** (`deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`),
**D2** (#99 seed-cranelift enum miscompile), **D3** (freestanding landmine family),
**D4** (the guide drift above).

## 2026-08-06 crt0 / linker / aarch64 real-firmware boot

- **crt0 module-init call was missing on both arches** — every module-level
  heap-backed global was previously silently uninitialized because
  `__simple_call_module_inits` was never invoked from userspace crt0. Fixed
  for x86_64 (`3525e837a0e`) and, separately, aarch64 (`1e9311483f7`, verified
  `75b7e20962c`). This directly caused an empty `.init_array` behind AC-6's
  `rc=70` failure, pinned in `b8360aea0e6` before the fix landed. Any future
  "reads as zero"/"nil where a static should be initialized" symptom on
  SimpleOS userspace should check crt0's module-init call is actually wired
  before assuming a MIR/codegen bug.
- **`operator new(0)` NULL bug** — see B1 bug-record row above
  (`13abfa0ca2f`); same `simpleos_cxxabi.c` file family as crt0.
- **ELF64→ELF32 silent linker downgrade** (`7c9609333fd`): `linker.rs`
  unconditionally objcopy'd every x86_64 freestanding kernel to ELF32/EM_386
  via crt0.s presence — correct for the legacy QEMU `-kernel` multiboot1 path,
  wrong for OVMF+GRUB-EFI+multiboot1 (AC-6), which needs ELF64. Gated behind
  `SIMPLE_FREESTANDING_ELF32_MULTIBOOT_WRAP=1` (default off) instead of
  unconditional. Same commit also fixed `check-simpleos-x86-kernel-elf.shs`
  unconditionally rejecting legitimate weak `spl_handle_*` syscall-stub
  fallbacks (~40 symbols, correct for an SSH-only entry closure).
- **aarch64 now boots through real firmware, mirroring x86_64's Limine
  pattern** — the aarch64 EFI-stub gap tracked since 2026-07-14 is closed.
  Provisioned real vendored Limine `BOOTAA64.EFI`/`BOOTX64.EFI` (v10.8.5,
  `vendor/limine/`, via `scripts/os/provision_limine_efi.shs`) and ported the
  Limine boot protocol to aarch64 (`c922fdef5d7`). Validated: both binaries
  boot for real under OVMF/AAVMF pflash with a minimal hand-written ELF probe
  kernel (not a PE/COFF stub) to serial output. Scoping doc for the prior gap:
  `028a2ae89ce`. **Next step for this feature, not yet done:** wire the full
  SimpleOS aarch64 kernel (not just the probe) through this same boot path —
  check for fresher commits before assuming this is complete.

## isa-debug-exit board-runnable sweep (2026-08-06)

A multi-commit sweep removed `isa-debug-exit` (a QEMU-only device with no real
hardware; see `.claude/rules/board-runnable.md`) from ~29 scripts across
`scripts/os/` and `scripts/check/`: `d022f71664e`, `a538b424f56`,
`76c95142d68`, `e9359cfd1ac` (fix commits) plus `cb92e6c0a5e` (closes a
`-kernel` board-runnable finding as a false alarm, adds dev-harness banners).
If a new QEMU launch script or probe is added, grep it for `isa-debug-exit`
before landing — this was previously a recurring, silent violation.

## Verification Requirements

- **Firmware proxy always:** OVMF pflash on x86_64, OpenSBI on riscv64. Never
  `-kernel` on x86_64, never `isa-debug-exit`.
- **Evidence = a retained serial/SSH transcript bound to the exact artifact by
  path + SHA-256.** A claim is not evidence; a commit-pinned historical proof is
  not a fresh lane's evidence.
- Key commands:
  - Cross toolchain: `bin/simple run src/os/port/llvm/build.spl`
    (stages `host-tools` / `cross` / `compiler-rt`; multi-hour — run detached
    with a log, never in a foreground timeout).
  - Simple payload: `sh scripts/os/simpleos-native-build.shs` with
    `SIMPLE_BUILD_COMPILER=src/compiler_rust/target/bootstrap/simple` (D1).
  - `-cc1` ladder: `SKIP_STAGE=0 SKIP_KERNEL=0 sh scripts/os/scp_retrieve_over_ssh_uefi.shs`
  - Link ladder (AC-5, never yet run): `sh scripts/os/ssh_lld_link_uefi.shs`
  - Install image + live gate: `sh scripts/os/build_simpleos_install_image.shs`
    then `sh scripts/os/ssh_simple_hello_uefi.shs` (rung L4b).
- Specs are fail-closed and `step()`-based; an unavailable row reports
  `blocked`, **never** `skip()`.

### SSpec ownership and claim boundaries (2026-08-16)

- `test/03_system/os/os_compiler_bootstrap_spec.spl` preserves libc and
  toolchain owner-path inventory as source-contract evidence only. It does not
  check the Rust seed or `bin/simple` and cannot prove bootstrap convergence.
- `test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl` exercises the
  production wrapper with controlled payload fixtures. It proves wrapper
  dispatch and no-host-fallback policy only.
- `test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl` exercises
  the production image builder's admission path. It proves rejection and
  staging contracts only.
- `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl` is the
  only umbrella live-guest acceptance spec. It must call the combined
  production wrapper and validate embedded, pre-boot, and same-run receipts.
- Keep each executable only under `test/03_system/os/` with its manual under
  `doc/06_spec/03_system/os/`. File inventories, test-only command emulation,
  and the Rust seed cannot promote any live row.

## Update Rule

When the project process creates or changes research, requirements,
architecture, design, tests, implementation, verification, or release artifacts
for this feature, update this skill with the new links and the current handoff
notes. In particular: when an AC moves, update the status table **and** say what
evidence moved it — several rows here are deliberately worded to prevent a
staging result being read as a self-host result, and a stale status line on this
page is worse than none.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`

## Restart12 Stage 4 prerequisite (2026-08-14)

The RV64 ordered boot gate cannot run on the Rust seed or Stage 2 compiler.
`doc/08_tracking/bug/stage3_selfhost_post_hir_segfault_2026-08-14.md` records
the current post-HIR Stage 3 crash; the log now reaches MIR method-call
lowering with a corrupt receiver local, so the earlier `error_count_value`
change is an avoidance, not a proved root fix. Resume through WP-A in the
canonical RV64 plan and require the fresh Stage 4 essential-tools smoke.
