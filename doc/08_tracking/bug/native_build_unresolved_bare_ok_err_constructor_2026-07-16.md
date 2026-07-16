---
id: native_build_unresolved_bare_ok_err_constructor_2026-07-16
status: SOURCE_RESOLVED_EXECUTION_PENDING
severity: high
discovered: 2026-07-16
area: compiler/native-build
related: src/os/drivers/nvme/_NvmeDriver/driver_operations.spl
related: src/os/services/vfs/vfs_boot_init.spl
related: doc/08_tracking/bug/simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14.md
---

# Native-build: bare `Ok(...)` / `Err(...)` Result constructors are unresolved → cr2=0x0 fault

## Resolution (2026-07-16)

Current Rust-seed lowering intercepts bare `Global("Ok"/"Err")` calls as
Result MIR instructions. Pure-Simple lowering admits the bare identifiers as
`NamedVar` calls and intercepts them as Result enum construction before
ordinary generic-call lowering. The existing cross-module
`Result<[u8], BytesError>` fixture now pins both bare constructors through the
default-LLVM and explicit-Cranelift entry-closure checker. Source and regression
coverage are present; executable verification remains pending.

This closes only the constructor-resolution hypothesis. The later NVMe field
and MMIO findings recorded below remain separate.

## Summary

Under the SimpleOS freestanding native-build, a BARE `Result` constructor call
— `Ok(x)` / `Err(x)` (the prelude-alias form) — is not resolved to a real
function in some modules. At runtime the guest prints `[WARN] unresolved fn: Ok`
/ `[WARN] unresolved fn: Err` and then faults with `cr2=0x0` (a call through a
null/unresolved function pointer). The QUALIFIED form `Result.Ok(x)` /
`Result.Err(x)` resolves correctly (the enum-variant constructor), and the same
modules use it successfully in ~200 other places.

## Evidence (live QEMU, 2026-07-16)

SimpleOS WM fullscreen harness, field-fix seed (`4dcca1aa27`) build. Serial:

```
[vfs-init] pure-nvme begin
[vfs-init] pure-nvme grant ok
[WARN] unresolved fn: Ok
[WARN] unresolved fn: Ok
[WARN] unresolved fn: Err
[vfs-init] pure-nvme lease policy degraded nvme-fs-transfer-not-ready:missing-nvme-doorbells
[WARN] unresolved fn: Ok
[fault] rip=0x00000000008c8d42 cr2=0x0000000000000000   # inside NvmeDriver.init_from_grant
...
[fault] rip=0x0000000000...     cr2=0x0                 # inside transfer_evidence_from_reversible_probe
```

ELF symbolization pins the faults inside
`os__drivers__nvme___NvmeDriver__driver_operations__NvmeDriver_dot_init_from_grant`
and `..._dot_transfer_evidence_from_reversible_probe`, both of which return
`Result` via bare `Ok(...)` / `Err(...)`. The faults are RIP+2-recovered
(non-fatal individually) but the boot never reaches framebuffer/desktop-ready —
so no render/PPM. `driver_operations.spl` had 22 bare sites (vs 200 qualified);
`vfs_boot_init.spl` had 65 bare (0 qualified) — exactly the executed pure-nvme
boot path.

## Root cause (hypothesis)

Native-build closure discovery / name resolution does not always bring the
prelude `Ok`/`Err` free-function aliases into a module's resolved symbol set, so
a bare `Ok(...)` call lowers to an unresolved extern that traps at runtime. The
qualified `Result.Ok`/`Result.Err` path goes through the enum-variant
constructor and is always resolved. This is adjacent to the documented
native-build closure-discovery limitations (`.claude/rules/bootstrap.md` §
"Native-Build Closure Discovery").

## Workaround (pure-Simple, applied)

Qualify every bare `Ok(...)`/`Err(...)` → `Result.Ok(...)`/`Result.Err(...)` in
the executed SimpleOS boot path (`driver_operations.spl`, `vfs_boot_init.spl`).
This is the unblock for the SimpleOS WM render; it does NOT fix the underlying
compiler resolution gap.

## Historical fix direction (implemented in current sources)

Current sources implement the root fix during MIR lowering, so bare
constructors no longer depend on prelude free-function aliases. Qualified forms
remain only a historical workaround; executable verification is pending.

## Update (2026-07-16 later): PRIMARY render blocker = NVMe init_from_grant MMIO fault-loop

Field-fix seed (`4dcca1aa`) harness runs still fail to render
(baseline_ppm_bytes=0, guest-render-fault). ELF-symbolized: the guest fault-loops
(~212 recovered cr2=0x0 faults) inside `NvmeDriver.init_from_grant`
(`driver_operations.spl`) at a `rt_volatile_write_u32` MMIO write to address 0 — a
doorbell/register write on an unmapped or zero BAR. `vfs_boot_init` reaches
`[vfs-init] pure-nvme grant ok` and NEVER returns (no framebuffer/desktop-ready),
so the desktop never renders. The null-BAR guard (`bar0_result <= 0` +
`bar0_virt == 0` -> Err) does NOT catch it, so SYS_MAP_BAR returns a
POSITIVE-but-unmapped vaddr (native-build BAR-mapping/MMIO infra gap) OR an inner
doorbell address computes to 0 during partial admin-queue setup.

A bare-Ok/Err qualification sweep (~270 sites, 17 files) was applied and cut the
runtime `unresolved fn` warnings 8 -> 4 and faults 245 -> 212, but did NOT unblock
render (the MMIO fault-loop is the real blocker) AND was lost to a concurrent peer
force-push before it landed durably. It is NOT worth re-running in isolation — the
bare-Ok/Err fix belongs in the compiler native-build lowering (root), and the
render needs the NVMe MMIO fault-loop fixed first.

SMALLEST unblock to a real PPM (peer owns the vfs/os lane; needs a fast-iteration
native-build host): make `init_from_grant` bail with Err BEFORE any doorbell/
register write when the mapped BAR is not real (verify SYS_MAP_BAR actually mapped
the page, or probe CAP without a faulting deref), so `_vfs_boot_init_pure_nvme_fat32`
(vfs_boot_init.spl:255, called from vfs_boot_init.spl:163->191) returns false and
the desktop degrades-no-disk and renders. The desktop already has degraded-no-disk
font/spawn guards, so this is the minimal path to a nonblank PPM.

## ROOT TRACE (2026-07-16 final): SYS_MAP_BAR maps, but the vaddr is unreachable from active CR3

Empirically ruled out source-level guards: NVMe-module `log_info`/`log_raw_println`
go to klog, NOT serial, so internal markers are invisible — and more importantly
the fault is at the MMIO **instruction** (mmio_read/write to the BAR vaddr), where
the kernel's RIP+2 fault-recovery corrupts execution before any Simple-level guard
(CAP-validity, bar0_virt==0) can run. A guard in `init_from_grant` therefore
cannot fix this; verified by adding a CAP==0/all-ones presence guard — the fault
persisted (still ~226 faults inside `init_from_grant`).

Traced to the root: `_handle_map_bar` (syscall 83, `syscall_device.spl:264`) is
CORRECT — it loops `vmm_map_page(virt, phys, VM_PRESENT|WRITABLE|CACHE_DISABLE|
NO_EXECUTE)` over the BAR pages and returns `base_virt` (from `_next_mmap_addr`).
So the BAR IS mapped into a page-table tree. Yet MMIO to that returned vaddr
page-faults with cr2=0x0 and the fault dumps show `cr3=0x18004000` (the FIXED boot
page tables). => The pages `vmm_map_page` establishes are **not reachable from the
active CR3** (the boot tables at 0x18000000/384MB), OR the mapping lands but the TLB
isn't flushed, OR `_next_mmap_addr` sits in a PML4/PDPT region absent from the boot
CR3. This is a VMM / page-table-reachability gap in the freestanding native-build,
NOT an NVMe-driver logic bug and NOT the field/Ok-Err issues.

NEXT (deep VMM kernel work, peer's os lane, fast-iteration host): use the existing
`_vram_mapping_probe` page-walk technique in
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` (it walks
PML4->PDPT->PD from the live CR3 for the framebuffer vaddr) to walk the NVMe BAR
vaddr returned by SYS_MAP_BAR and confirm whether the PT entry is present under
cr3=0x18004000. If absent: `vmm_map_page` must map into the ACTIVE boot CR3 (or the
boot must switch to the vmm-managed CR3) and flush TLB. Fixing SYS_MAP_BAR's
mapping-reachability unblocks REAL NVMe -> FAT32 mount -> full SimpleOS render with
font+apps (not just degraded). This is the single remaining blocker for the
SimpleOS showcase surface.

## CORRECTION (2026-07-16): CR3-reachability theory is WRONG — it's self.bar0_virt reading 0

The prior "unreachable from active CR3" conclusion is retracted. The VMM bootstrap
root logged at boot is `402669568` = `0x18004000`, which is EXACTLY the fault
`cr3=0x18004000`. So `vmm_map_page` (called by `_handle_map_bar`) maps into the
ACTIVE CR3 tree — the BAR vaddr IS reachable. And the fault is `cr2=0x0` (access to
address **0**), NOT to the mapped BAR vaddr. If the MMIO used a valid `self.bar0_virt`
(the positive value SYS_MAP_BAR returned), cr2 would be that vaddr, not 0.

=> The real pin: **`self.bar0_virt` reads as 0 at the MMIO site** even though
SYS_MAP_BAR returned positive and the null-BAR guard (`self.bar0_virt == 0` right
after assignment) passed. That means either (a) the field WRITE
`self.bar0_virt = bar0_result.to_u64()` does not persist across subsequent method
calls in the native-build (a field-mutation-persistence codegen bug), or (b) a
cross-module read of `self.bar0_virt` (e.g. via the mmio helpers /
`nvme_sq_doorbell_addr`) resolves to a different/zero slot — the SAME
native-build cross-module field-resolution family as the FramebufferDriver shift
(bug simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14).
The seed field fix `4dcca1aa` fixed FramebufferDriver READS but evidently not this
NvmeDriver case (more fields, and possibly the WRITE side).

NEXT: add a `serial_println` (NOT klog log_info/log_raw — those don't reach serial
in freestanding) at (1) right after `self.bar0_virt = ...` and (2) at the first
`mmio_*(self.bar0_virt + ...)` site, printing `self.bar0_virt` each time. If it
prints positive then 0, it's field-persistence; if the doorbell helper sees 0 for
a positive param, it's the cross-module shift. Then fix accordingly (thread
bar0_virt as an explicit scalar param through the MMIO sites, mirroring the
FramebufferDriver executor scalar-threading workaround, OR fix the seed field
codegen). This unblocks NVMe -> FAT32 -> full SimpleOS render.

## MAJOR PROGRESS (2026-07-17): NVMe blocker SOLVED; render now blocked at bga port_outl hang

Two fixes landed the boot much further:
1. NVMe I/O-not-ready degrade guard (`fix(os/vfs)`, ON ORIGIN): `_vfs_boot_init_pure_nvme_fat32`
   now returns false when `transfer_evidence.doorbells_mapped`/`io_queue_ready` are false,
   instead of proceeding to a FAT32 DMA read that doorbell-writes to null and fault-loops.
   VERIFIED: boot advances past vfs-init to `[desktop-gui] initializing framebuffer...`,
   faults 113->5, `[vfs-init] pure-nvme io not ready — degrading to no-disk`.
2. (also confirmed: NVMe bar0_virt is VALID (0xFEBD0000) and CAP read SUCCEEDS — the earlier
   "self.bar0_virt reads 0" correction was itself wrong; MMIO to the BAR works. The NVMe issue
   was purely that doorbells never came up, so I/O degrades — not a mapping/field bug.)

REMAINING render blocker (precisely pinned via serial markers): the boot reaches
`bga_init_framebuffer` -> `enable_vga_pci_decode` -> `pci_config_read32(0,0,0,0)` and HANGS at
`port_outl(0x0CF8, 0x80000000)` — the marker before the call prints, the marker after does NOT.
An OUT instruction cannot hang at the CPU level, and `rt_port_outl`/`rt_port_inl` ARE defined in
the ELF (0x10ce00/0x10ce90, not unresolved), so this is a NATIVE-BUILD CODEGEN issue on the 32-bit
PCI-config port-I/O path that the peer's `bf3d89e755 feat(wm): harden ... fullscreen rendering`
ADDED (enable_vga_pci_decode + find_bga_pci_device via port_outl/port_inl). The pre-`bf3d89e755`
bga used 16-bit `port_outw`/`port_inw` (which work); early "reached scanout" harness runs used a
CACHED pre-regression kernel. The u8 loop-counter (`while dev < 32`) was NOT the cause (fixing it
to i64 did not help; reverted).

NEXT (peer's os/wm lane — bf3d89e755 regression): fix the native-build codegen for the
`port_outl(u16, u32)` call in the freestanding bga path (compare the working 16-bit `port_outw`
lowering), OR have bga fall back to the 16-bit I/O-port path + fallback LFB (0xFD000000) instead
of the 32-bit pci_config scan, so `bga_init_scanout` returns and emits `[scanout-evidence]`. That
is the last step to a real SimpleOS WM PPM — the boot otherwise reaches framebuffer init cleanly.

## SESSION ARC (2026-07-17): SimpleOS WM boot driven from crash to first-frame render

Rebuilding the seed from current source (`cargo build -p simple-driver`) FIXED the
32-bit PCI-config `port_outl` hang (a stale-seed codegen bug, now fixed upstream) —
bga completes, `[scanout-evidence] 3840x2160` emits, framebuffer is writable
(`[vram-probe] write-readback` ok). With that, the boot advances through the FULL
init and into the first-frame render. A chain of fixes cleared successive blockers:

1. `io not ready` degrade guard (vfs_boot_init) — NVMe I/O-not-ready → degrade no-disk.
2. `rt_file_read_bytes` weak stub returns empty [u8] instead of halting.
3. font_renderer: two module-level `val: Mutex = mutex_new(0)` → raw handles behind
   `var: Any = 0` (literal-init works on baremetal; function-call-init does NOT).
4. FontRasterizer.load: dlopen viability gate FIRST (bail before font-asset access).

Each fix moved the fault deeper. Faults: 226 → 5 → (fresh seed) → 10 → 5 → 4 → now
the render itself. **Final fault (this session): a NULL FUNCTION-POINTER call in the
render path** — `DesktopShell.render_baremetal_first_frame → Engine2dWmFrameExecutor.render
→ engine2d_draw_ir_adv_composition_present_with_images → ...render_batch_embedded →
render_commands → _engine2d_draw_ir_render_box` jumps through null (RIP walks 0x100+).

## SYSTEMIC ROOT (confirmed): missing freestanding module-init

Every one of these is the SAME defect: on the freestanding/baremetal native-build,
module-level globals with a **function-call initializer** (`mutex_new(0)`, and any
global holding a function/closure ref or a registry built at init) are NOT run —
only **literal** initializers (`0`, `[]`, `nil`, `""`) execute at module-init. So
those globals stay null and any deref / call-through-them faults (cr2=0x0 or a
null-function-pointer jump). The native-build emits globals as static LLVM constants
(core_codegen.spl:122) but does not emit+call a `__module_init` that runs the
non-constant initializers for lib modules. This is an UNBOUNDED cascade across the
font + engine2d render stacks — per-site workarounds (raw-handle-literal-0, dlopen
gate) each clear one site but reveal the next.

**The real fix is native-build codegen: generate a module-init routine that runs
every function-call/non-constant global initializer (in dependency order) and call
it from the boot entry (the main shim already calls `__module_init`; it must cover
lib modules).** That single fix unblocks the whole cascade and the SimpleOS WM render.
Until then, the boot reaches the first-frame render but faults through uninit-global
function pointers in `_engine2d_draw_ir_render_box`. NVMe/port_outl/file-read/font
blockers are all cleared and on origin.

## CONCLUSIVE ROOT (2026-07-17): the module-global-init gap is KNOWN + DOCUMENTED (mutglobal_plan.md)

Traced the systemic module-init blocker to its exact, already-documented source in
`src/compiler/50.mir/_MirLowering/module_lowering.spl:645-698`:
- `lower_const` lowers EVERY module-level `val`/`var` into `MirModule.constants` as a
  CONSTANT-FOLDED value. A function-call initializer (`mutex_new(0)`, a font registry
  built at init, a render-dispatch function ref) cannot be folded to a constant, so it
  becomes null / zeroinitializer.
- `lower_static` populates `MirModule.statics` for the mutable subset but ALSO only
  stores a constant-folded `init` (nil for a function call), and the code comment
  (lines 659-668) explicitly documents the remaining gap: "nothing downstream READS a
  global's address for an identifier reference ... or WRITES to one ... wiring an actual
  read/write through it is the documented follow-up." Plan: `scratchpad/mutglobal_plan.md`.

So the SimpleOS WM first-frame render is blocked by the KNOWN, PLANNED mutable-/
non-constant-global-init feature — NOT a per-site bug. Completing it requires: preserve
the non-constant init EXPRESSION (don't fold to null), synthesize a per-module init
routine that evaluates it and stores to the global, emit + call `__module_init` from the
boot shim (which already calls it if present), and wire identifier read/write through the
global storage — in dependency order, gated to freestanding to protect the 3-stage
bootstrap determinism. This is the single fix that unblocks all 4 SimpleOS showcase cells.
Six per-site fixes this session drove the boot from crash to the first-frame render; this
documented compiler feature is the remaining work.
