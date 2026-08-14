# SimpleOS Kernel Exec / Loader Layer Expert

## Role

Own layer-specific process knowledge for the SimpleOS **execution substrate**:
the VMM / address-space publication, the FS-exec ring-3 loader that actually runs
guest binaries, the SMF loader, the FAT32 guest filesystem, the syscall dispatch
split between the kernel and the `_bare_exec` fast path, and the install-image
builder that stages payloads into a bootable disk.

This is the layer that decides whether an on-disk `x86_64-unknown-simpleos` ELF
becomes a running ring-3 process. Its sibling
[llvm_toolchain_port](../llvm_toolchain_port/skill.md) decides whether that ELF
has the right *shape*.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Layer Links

- **VMM:** `src/os/kernel/memory/vmm_core.spl` (`_vmm_pml4_phys` :177, accessor
  :191-192, `vmm_publish_kernel_pml4`), `vmm_address_space.spl` (guard :75, also
  :91, :119), `src/os/kernel/arch/x86_64/paging.spl:214` (**the live
  initializer**, stores at :230).
- **FS-exec loader:** `src/os/kernel/loader/x86_64_fs_exec_ring3.spl`
  (`_x86_64_fs_exec_enter_ring3` :311, `arch_x86_64_enter_user_task` :437,
  blocks until `exit(2)` :449), `x86_64_fs_exec_spawn.spl` (SpawnWait handler),
  `fs_exec_resolve.spl`, `smf.spl` (code-complete, **zero in-guest usage**).
- **Syscalls:** `src/os/kernel/ipc/syscall_process.spl` (`_handle_fork` :237,
  `_handle_exec` :252 — Fork 57 / Exec 59), `src/os/kernel/abi/syscall_shim_file.spl`
  (`spl_handle_fork` :415, `spl_handle_exec` :426), `src/os/kernel/ipc/syscall.spl`
  (mmap base `0x50000000`), and the `_bare_exec_handle` fast path in
  `baremetal_stubs.c`.
- **Filesystem:** `src/os/kernel/fs/fat32.spl`.
- **Image builder:** `scripts/os/build_simpleos_install_image.shs`,
  `build_simpleos_install_image_main.spl`, `src/os/installer/image_builder.spl`
  (`_validate_simple_binary` :886, call site :218),
  `scripts/os/make_os_disk.shs` (`validate_simple_payload_provenance` :52),
  `make_os_disk.c:460` (appends the 128-byte `SMF` trailer).
- **Memory layout (load-bearing):** kernel links at 128 MB
  (`examples/09_embedded/simple_os/arch/x86_64/linker_128mb.ld`), `.bss`
  `[0x08000000, ~0x16400000)`; ring-3 link base `0x40000000`; mmap `0x50000000`.
  Clang lanes need `QEMU_MEM=2G`+.
- **Fabricated-stub channel:** `config/freestanding_fabricated_stub_baseline.sdn`,
  `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:299-314`.
- Downstream feature expert:
  [simpleos_toolchain_selfhost](../../feature_expert/simpleos_toolchain_selfhost/skill.md).
- Adjacent (do not duplicate their scope):
  [os_compositor](../os_compositor/skill.md),
  [feature_expert/simpleos_wm_qemu_evidence](../../feature_expert/simpleos_wm_qemu_evidence/skill.md).

## Load-Bearing Facts (2026-08-06)

1. **There were two parallel VMM implementations printing byte-identical
   `[VMM]` banners.** The live init is `arch/x86_64/paging.spl:214`, writing its
   own `g_vmm.pml4_phys`; `vmm_core.spl`'s `vmm_init`/`vmm_init_from_global_pmm`
   (:273, :282) are **dead code with zero callers**, so `_vmm_pml4_phys` was
   never written. Consequence: `vmm_kernel_pml4_phys()` read 0 after a
   *demonstrably successful* init, `create_user_address_space` fell back to the
   legacy sentinel, and **every** FS-exec ring-3 spawn returned `rc=-1`. Fixed by
   `vmm_publish_kernel_pml4(pml4_phys, hhdm_offset)` (+35 lines, 2 files, commit
   `4575b4ce88d`). **The two implementations are still not consolidated.**
   - The fix sets three **scalars** (`_vmm_pml4_phys`, `_vmm_hhdm_offset`,
     `g_vmm_initialized`) rather than the struct, because `g_vmm` is a struct
     global with a constructor initializer — an unreliable freestanding category
     (**D3**, `doc/07_guide/os/baremetal_simple_codegen_landmines.md`).
   - Failure markers: `[VMM] create_user_address_space: VMM not initialized —
     legacy AS=1`, `[spawn] FAIL user-AS synthetic root=1`, `rc=-1`.
   - Success marker: `[VMM] portable VMM published kernel PML4 0x402718720`.
   - **Do NOT relax the `vmm_address_space.spl:75` guard.**
2. **fork is UNREACHABLE, not broken — for two independent reasons.**
   (a) `x86_64_fs_exec_ring3.spl:311` hand-builds the address space and `iretq`s
   via `arch_x86_64_enter_user_task` without `create_task` / `TaskId` /
   `register_task_vmspace`, so `sched.get_current()` has no task to clone.
   (b) `rt_user_heap_init` sets `_bare_exec_mode = 1`, and `rt_syscall_dispatch`
   offers **every** syscall to `_bare_exec_handle` FIRST; its switch covers
   `0, 4, 10, 11, 12, 15, 30–34, 39, 43, 44, 46, 47, 50, 60, 69` — **no 57, no
   59, no 61**. Fixing one reason alone changes nothing.
3. **What landed instead is SpawnWait = syscall 120.** Deliberately not 57/59,
   and **not 70** (already `net_socket`; using it produced a duplicate `case`
   label). ABI: `a0` path ptr, `a1` path len, `a2` NUL-separated argv blob,
   `a3` blob len, `a4` argc. The single-slot savepoint became a stack
   (`_ring3_resume_depth`, `RING3_RESUME_MAX_DEPTH = 4`). **cr3-restore
   correctness is reasoning-only, unverified.** Related still-live constraints:
   `_bare_exec_halt_on_exit = 1` (case 0 does `outb(0xF4)`) and a shared RAM file
   table reset by `_bare_exec_reset_files()`.
4. **Guest FS is FAT32, root-directory-only, 8.3 names.** LFN is parsed;
   subdirectory *read* traversal landed (17/17 spec, sabotage-verified). Stage
   in-guest files as `HELLO.O`, `LLD.ELF`, `LIBC.A` in the root. FAT32
   subdirectories in the image are created **host-side** (`alloc_directory`,
   `put_named_dir_entry`), not by the guest.
5. **The SMF loader has zero in-guest usage** — code-complete is not proven.
   Staged `.smf` files are currently bare ELF with **no** 128-byte `SMF` trailer,
   so any SMF-envelope claim needs its own marker evidence.
6. **Ring-3 execution under real firmware is proven for clang** (OVMF pflash,
   never `-kernel`): `[ok] L3 sshd ring-3 accept loop`,
   `[ok] L4 in-guest clang compiled /hello.o under OVMF`,
   `[oo-nvme] persist /hello.o -> OK`, `[syscall] exit status=0`. In-guest LINK
   and RUN of a linked program are **not** proven.
7. **Handoff — the SpawnWait in-guest proof is now UNBLOCKED.**
   `doc/08_tracking/bug/fs_exec_ring3_fork_unreachable_spawnwait_2026-08-06.md`
   still records its in-guest proof as blocked by **D6** — but D6 was fixed the
   same day (fact 1, commit `4575b4ce88d`), and ring-3 spawn now demonstrably
   works. So the SpawnWait proof is a *runnable next step*, not a blocked one;
   the bug doc's blocked status is stale. Re-run
   `sh scripts/os/build_spawn_wait_ring3.shs` and update that doc. Note its
   secondary blocker was independent of D6: the guest got stuck in
   `[tcp-accept] EAGAIN` (virtio-net stall), so budget for that separately.

## Traps Owned by This Layer

- **A log marker that does not identify its WRITER cannot distinguish two
  implementations.** Before trusting a `[VMM]`-style banner, confirm the
  *consumer* reads the global the *writer* wrote, and grep for callers of the
  initializer — a zero-caller `*_init` is dead code posing as the live path.
  Rule out the cheap hypotheses **with evidence** first, as was done here:
  `nm` found exactly ONE `_vmm_pml4_phys` (no duplicate `.bss`) and `objdump`
  showed a real accessor body (`mov $0x80c4138,%rdi; mov (%rdi),%rax; ret`), not
  a stub.
- **The fabricated-stub guard FAILS OPEN for an entry with no baseline rows.**
  `freestanding_fabricated_stub_baseline.sdn` has zero rows for
  `simpleos_ssh_ring3_uefi128.elf`, and `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:299-314` only **WARNS** for an
  unbaselined entry. Under `SIMPLE_ALLOW_FREESTANDING_STUBS=1` a source file that
  fails to build is replaced by a weak no-op body — a **green build with dead
  code**. It happened: prose after the closing `*/` in `enter_user_first.s`
  stopped it assembling and the build stayed green with a no-op `iretq`.
  → Accept a kernel fix only on a **POSITIVE** marker
  (`[oo-nvme] persist /hello.o -> OK`), **never** on the absence of a failure
  line — a stub satisfies every absence condition. Additionally `nm` the ELF and
  require `T`, not `W` (`rt_x86_enter_user_first` reading `W`, with
  `_ring3_resume_buf` absent, was the tell, alongside
  `FABRICATED-NEW spawn_wait_ring3.elf rt_x86_enter_user_first`). For assembly,
  assemble standalone: `clang --target=x86_64-unknown-elf -c`. Diff the
  `FABRICATED-NEW` set before vs after every kernel change and baseline the entry
  on a known-good PRE-fix build to make it a ratchet.
- **Image-builder provenance: the WEAKER guard ran FIRST.** The Simple
  `_validate_simple_binary()` checked only `target=`/`entry=`/`entry_closure=` +
  ELF magic/class/machine, while the shell
  `validate_simple_payload_provenance()` also checks stamp freshness,
  `backend` ∈ {llvm, cranelift}, and rejects a `compiler` matching
  `*compiler_rust*`/`*simple_seed*`. Because the weak one ran first, **12
  seed-built role files were staged into the rootfs** before the shell layer
  refused with `invalid SimpleOS Simple payload build stamp compiler: …` /
  `Error: FAT32 disk generation failed; refusing non-bootable descriptor
  fallback`. That refusal is the guard **working**; the defect was the staging
  before it. Host `bin/simple` and marker apps are never pass evidence — assert
  the payload SHA-256, not just path presence.
- **`s[i] as u8` on `text` silently yields ZERO under `bin/simple run`**, which
  produced a structurally valid FAT32 boot sector
  (`BPS=0200 SPC=01 reserved=20 FATs=02 root_cluster=02`) with an all-NUL OEM
  field and dirent name. Assert byte *content* of generated on-disk structures,
  never only parseability.
- **Guest-run Simple code must use index loops, not `[s:e]` + `join`** (D3
  freestanding landmines: module-global array initializers never run,
  `rt_string_join` faults, `text_index_of` nil).

## 2026-08-06 landings

- **FAT32 `rename_at` + fd-table wiring** (`f92f60da224`, `cf12235211a`):
  `Fat32Filesystem.rename_at` is a real primitive (not a stub); path-based FS
  syscalls now go through `fat32_fd_table.spl` for read/write. Also this
  session: FAT32 delete left LFN slots live, re-adopting deleted long names
  (`d4692cb181d`); 8.3 short-name generation aborted on non-ASCII filenames
  (`c5c77454cce`). New mount-accessor persistence wall documented (not yet
  fixed) — see `doc/08_tracking/bug/` FAT32 mount-accessor docs, and
  `52ede2e5a72` (confirms Wall 2 is a pre-existing seed-only Optional-bind COW
  defect, not new).
- **Scheduler/IpcManager state-loss fix** (`7e36d9a577a`): process syscalls
  were reading/mutating *copies* of `Scheduler`/`IpcManager` state (value-copy
  semantics on a struct silently drops writes across the call boundary) — fixed
  by threading a `ProcessSyscallState` wrapper through every process syscall
  path. `execve_spec.spl` went to 8/8 as a result. This is an instance of the
  general "structs are value types" trap — any future kernel syscall handler
  that takes a scheduler/IPC struct by value instead of through this wrapper
  will silently lose state the same way.
- **ENOEXEC symbol-collision fix** (`6972b397244`): `byte_utils.spl`'s
  `read_u16/32/64_le` collided across modules at link time (ELF64 reader vs
  something else), producing ENOEXEC. Renamed to `lb_read_*_le`. Any new
  cross-module free function with a generic name (`read_*`, `write_*`) should
  be checked for this class of collision before landing.
- **C-ABI syscall shim spec coverage** (`399546e466c`): first real spec for
  `syscall_shim_process.spl`/`syscall_shim_file.spl` — calls the `@export("C")`
  entry points directly and verifies `g_shim_scheduler = st.scheduler`
  state-threading is genuinely wired (spawn_binary, waitpid), not just
  compile-checked. In writing it, a new interpreter bug was found and filed:
  `doc/08_tracking/bug/shim_init_keepalive_function_ptr_cast_breaks_interpreter_2026-08-06.md`
  (function-pointer-to-`u64` cast unsupported in the tree-walk interpreter) —
  check that doc for current status before assuming it's fixed.

## 2026-08-07 landing: aarch64 `@repr("C")` global-struct field-read status update

The aarch64 real-firmware global-struct field-misread defect (tracked in
`doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`)
has a narrower root-cause set as of `606bae83998`:

- **Workaround remains live** — no change to the runtime mitigation.
- **One suspected cause was investigated and REFUTED**, not confirmed: MIR
  lowering's `try_lower_global_read` was missing a `struct_value_syms`
  provenance registration (real gap, now fixed — see
  [layer_expert/mir_lowering/skill.md](../mir_lowering/skill.md)), but a
  discriminating `SIMPLE_MIR_FIELD_TRACE=1` probe showed x86_64 JIT already
  covers this read via the HIR-type fallback, independent of that map. So this
  gap is NOT the aarch64 cause.
- **Root cause narrowed to two Cranelift-side candidates**, both still
  unverified: `GetField`'s uniform 8-byte field stride (wrong for
  sub-8-byte-aligned fields), and an unconditional `band(addr, -8)` tag-strip
  applied to every struct-field address regardless of the field's actual
  alignment.
- **Verification of either candidate is still blocked** on the same
  native-build SIGSEGV this layer already tracks (fact/trap section above;
  `doc/08_tracking/bug/mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06.md`).
  Do not attempt to close this defect without a native build that survives
  past first call.
- **A regression spec now exists**:
  `test/01_unit/compiler/global_c_repr_struct_field_read_spec.spl` — exercises
  the `try_lower_global_read` fix path directly, but does not by itself prove
  the aarch64 field-misread fixed (different engine, currently unreachable per
  the SIGSEGV blocker).

## 2026-08-07 landing: WP-21, `exec_cap_check` gets real logic, caller identity still not threaded

`src/os/kernel/loader/cap_exec_gate.spl`'s `exec_cap_check(caller, path)` used
to build a fresh, empty `os.kernel.ipc.capability.CapabilityManager` per call
(`records: []`), so ANY nonzero caller was unconditionally denied — not
"checked", stuck permanently at deny regardless of real capabilities. The old
header comment ("this gate never denies") was backwards and incomplete: an
always-empty manager can also never allow, which made a deny-only spec
against it vacuous.

- **Fixed:** added `exec_cap_check_caps(caps: CapabilitySet, path: text) ->
  i32` — real logic on `CapabilitySet.has(...)`, the SAME model
  `TaskControlBlock.capabilities` / `spawn_authority.spl` already use in
  production (not the dead `ipc.cap_manager`/`TaskCapRecord` store — see the
  sibling `execve_spec_blocked_by_dead_ipc_cap_gate...` bug doc, a DIFFERENT
  dead capability store than this one). Proven both directions,
  sabotage-verified: `test/01_unit/os/kernel/loader/cap_exec_gate_spec.spl`, 8/8.
- **Still open:** threading a caller's real `CapabilitySet` into
  `exec_cap_check(caller: i64, ...)` itself. None of `fs_exec_spawn_as` /
  `fs_exec_spawn_with_recipe` / `fs_exec_spawn_ring3_with_recipe`
  (`fs_exec_spawn.spl`) carry a `Scheduler`/`TaskControlBlock` handle — the
  fs-exec bridge builds its own throwaway bootstrap `Scheduler` internally
  (`_fs_exec_new_bootstrap_scheduler`), so there is nowhere to look up
  `caller`'s real capabilities from. Full detail + the reachability audit
  (confirmed: no userspace-reachable path calls the caller-less wrappers
  today, only kernel console shell-launch and boot probes do) in
  `doc/08_tracking/bug/exec_cap_check_caller_identity_not_threaded_2026-08-07.md`.
- **Found along the way, not this layer's gap:** the REAL userspace-reachable
  exec/spawn syscalls (`_handle_exec_state`, `_handle_spawn_binary_state`,
  `_handle_spawn_state` in `src/os/kernel/ipc/syscall_process.spl`) already
  thread genuine caller identity via `scheduler.get_current()`
  (`_ambient_spawn_caller` :106) — they never go through `fs_exec_spawn` at
  all. `Scheduler.get_current() -> TaskId`
  (`scheduler/_Scheduler/scheduler_lifecycle.spl:355`) is a real, already-used
  current-task-identity primitive; it just isn't reachable from inside the
  fs-exec bridge's own throwaway scheduler.
- **`minimum_assurance` gating via `SimpleArtifactManifest` (WP-19, `53c5eb96997`):
  checked, absent.** `SimpleArtifactManifest`'s fields
  (`src/os/kernel/loader/artifact_manifest.spl:198-207`) have no
  assurance/minimum_assurance field — not more tractable than the
  caller-identity route, just a different gap.

## Verification Commands

```sh
# ring-3 / boot gates — OVMF pflash always, never -kernel, never isa-debug-exit
sh scripts/os/ssh_ring3_uefi_boot.shs                 # "PRIMARY GATE PASS: sshd accept loop started under OVMF"
SKIP_STAGE=0 SKIP_KERNEL=0 sh scripts/os/scp_retrieve_over_ssh_uefi.shs   # in-guest -cc1 ladder
sh scripts/os/ssh_lld_link_uefi.shs                   # rungs 3-6: in-guest LINK + RUN (NEVER YET EXECUTED)
sh scripts/os/ssh_simple_hello_uefi.shs               # rung L4b: /usr/bin/simple /hello.spl
sh scripts/os/build_simpleos_install_image.shs disk --arch=x86_64
sh scripts/os/build_spawn_wait_ring3.shs              # SpawnWait probe
```

Live SSpec: `test/03_system/os/simpleos_guest_toolchain_live_spec.spl` (needs
`SIMPLEOS_QEMU_SSH_TOOLCHAIN_LIVE=1`, `sshpass`, and a baked
`build/os/simpleos_disk.img`). Specs are fail-closed and `step()`-based; an
unavailable row reports `blocked`, never `skip()`.

Reject any run containing `spawn:preloaded`, `HOSTED_NETWORK_UNAVAILABLE`,
`FABRICATED-NEW`, or `guest-toolchain-exec-gate BLOCKED`.

## Update Rule

When this layer's public contract (address-space publication, FS-exec entry,
syscall numbering, FAT32 capability, image-staging provenance), source
ownership, tests, or verification requirements change, update this skill with
the new links and handoff notes. Record explicitly which of the facts above a
change *invalidates* — several are corrections of earlier claims, and a stale
fact here is worse than none.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`

## RV64 boot ownership contract (2026-08-14)

For `rv64-ssh`, the boot orchestrator must consume runtime facts owned by
paging (Sv39 SATP readback), PM/scheduler (PID1 create+liveness), VirtIO
(TX/RX/service), SSHD (bind/listen and accept recovery), and compositor
(PID-correlated present). It must not synthesize these facts from later
markers. The shared ordering and negative-test plan is
`doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md`.
RV64 SSH execution now uses attempt-local bounded stdout/status capture,
including empty output, nonzero status, and truncation; a pre-launch failure
must reset prior capture. Source is complete, but TODO808 remains open until an
admitted Stage 4 runner executes the focused cases and TODO806 retains the
independent live OpenSSH outcomes. Canned output and stale global capture are
never evidence.
The source transport now owns syscall-18 destroy, live named-service discovery,
anonymous reply-port teardown, bounded byte-zero VFS frames, public FS binary
decoding, manager-routed mutations, and FD VFS READ/WRITE/SEEK/close. The Terra IPC handoff focused PASS is terminal-only and therefore diagnostic;
it does not close TODO809 or establish a source-matched runtime. The next
focused IPC command must retain output and Stage 4 provenance before handoff to
the root reviewer.

P1c freezes `IPC_COPIED_SERVICE_TAG` as the only copied-send discriminator;
all non-tag traffic, including zero-length sends, remains legacy. Syscall 18
may destroy only a live caller-owned port. The VFS close owner uses a monotonic
issued-handle watermark for bounded idempotence: a terminal close/replay
succeeds, but a lost reply keeps the final FD available for retry; `dup2`
records remote cleanup failure while preserving local replacement. SOSIX I/O
uses the shared named VFS READ/WRITE/SEEK path. Run and retain the plan's five
P1c focused rows only after TODO667; they are not a substitute for TODO806's
source-matched QEMU/OpenSSH evidence.
## Restart12 image/exec contract (2026-08-14)

The current image owner must emit embedded
`simpleos_toolchain_deployment_manifest` component identity and a separate
external `simpleos_toolchain_image_admission_receipt` after the image closes.
The planned combined desktop/toolchain wrapper is
`scripts/check/check-simpleos-toolchain-desktop-boot.shs`; it remains absent and
B-DESKTOP-LIVE. One OVMF/GRUB `gui_entry_desktop.spl` lifetime must bind
desktop/scanout/framebuffer and mounted-filesystem toolchain execution to the
same kernel/image hashes. Canonical details and blocker truth:
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.

Final cycle 3 completed current-source Stage 2 (binary SHA-256
`e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`,
log SHA-256
`db7907064858b472ffadf3cc9527f73acfaf4e80a5f3156d203ba84b924fb167`).
Host `earlyoom` terminated Stage 3 at 41,394 MiB RSS on a no-swap host with
less than 10% free memory; exit 143 followed 5.4 seconds later. TODO666 owns
one unchanged resume on a host with enough memory or swap; no fourth fix cycle
is permitted. TODO667/A2 remains gated. After a provenance-admitted Stage 4
exists, this layer's stdout/SSH evidence may run in parallel with the
disjoint IPC/VFS, boot-owner, WM, and manual rows. The source now keeps the
daemon accepting after WM admission and rejects later accepted sessions that
do not complete and resume accept; this remains unexecuted. Only the primary
RV64 owner runs the shared port-2222 live gate.
