# Entry-closure freestanding cranelift codegen defects found chasing first desktop frame (2026-07-16/17)

All found on `native-build --entry-closure --target x86_64-unknown-none --backend cranelift --opt-level=aggressive`
building `gui_entry_desktop.spl`. Each verified by objdump disassembly of `build/os/_wk/desktop.elf`.

## C1. Module-global `val/var X = call()` initializers never emitted
- Binary evidence: `_browser_default_font_lock` (font_renderer.spl:127) had 15 code refs, ALL uses,
  zero init stores; no init function anywhere. Global stays nil -> first `Mutex.lock` derefs nil self
  (cr2=0x0) -> recoverable-fault storm per text draw -> heap exhaustion.
- Also hits `[]`-initialized array globals (e.g. the new `_engine2d_cpu_offscreen_pool` reads len 0 /
  loses pushes).
- Workaround shipped: `font_renderer_ensure_runtime_locks()` called from gui_entry_desktop before
  first font use; hosted paths still run normal initializers.

## C2. `if val x = opt:` binding returns nil on the hit path
- Disasm of accessor: hit path compiled to `xor rax,rax; ret` (returns nil) while the miss path
  correctly returned the freshly created value. Same-shape failures previously seen inside
  `FontRasterizer.load` (`if val candidate = selected:` -> candidate nil -> `candidate.sha256`
  cr2=0x0).
- Note `.?` is (by design) the existence predicate `rt_is_some` -> bool; not an unwrap.

## C3. Short-circuit `and` drops its left operand when RHS is a call
- `if not registered_only and renderer.try_load_runtime_ttf(font_path):` compiled with NO test of
  `registered_only`; the call executed unconditionally (disasm 0xacb4bc..0xacb4cd: jne on the
  registered.1 test falls straight into the try_load_runtime_ttf call).
- Workaround shipped: nested `if not registered_only:` / `if renderer.try_load_runtime_ttf(...)`.

## C4. Anonymous tuple returns: positional member reads swapped
- `_engine2d_draw_ir_render_commands -> (Engine2D, i32, i32, text)`: caller's `.1` read the real `.2`
  and vice versa (probe: loop rendered a rect, `isrect=1`, yet outcome read r=0 s=1). Made a fully
  rendered frame report rendered=0 -> WM executor rejected the frame -> black screen.
- Same class as the documented interpreter "anon-tuple-return garbage" landmine.
- Workaround shipped: `Engine2dDrawIrRenderOutcome` struct replaces the tuple in draw_ir_adv.spl.
- 2-tuple `( [u8], bool )` returns (`_registered_selected_font_bytes`) likely affected too (unverified).

## Also observed (not yet root-caused)
- ~2 nil elements inside `batch.commands` arrays reaching render (nil-receiver ud2 panics x6 each)
  before the tuple fix; defensive `if not command.?: skip` added in render_commands.
- Fault-recovery scheme (baremetal_stubs.c `_rich_fault_entry`) advances RIP by fixed 2 bytes with
  rax=3; any fault on an instruction of another length resumes mid-instruction -> garbage execution
  (source of the 32.5MB rt_string_concat allocations that exhausted the heap).

## Second wave (2026-07-17, NVMe/vfs lane, same build config)

## C5. Enum `==` comparison miscompiles (match works)
- `lease.mode == NvmeNamespaceMode.System` false for a genuine System value while a match-based
  helper in the SAME frame prints `mode=system`. Misrouted the boot lease to
  `nvme-fs-user-namespace-uses-reserved-queue`.
- Workaround landed: match-based predicate `nvme_namespace_mode_is_system()`
  (src/os/drivers/nvme/nvme_storage_model.spl).

## C6. Fused byte-combine drops the second term when inlined
- `b0 | (b1 << 8)` (and `b0 + b1*256`, incl. named-intermediate forms) loses the high-byte term
  when inlined into the FAT dirent scan: first-cluster 0x0f70 read as 0x70 -> exec probe read the
  wrong cluster -> `exec probe failed` -> `mount_failed` -> bitmap font + 0 apps. HEISENBUG: adding
  debug prints makes it compute correctly.
- Workaround landed: single opaque loads `mmio_read16/32(addr+off) as u32`
  (src/os/services/vfs/vfs_boot_init.spl `_vfs_boot_mem_u16_le`).

## C7. Bare `.to_u32()` on u16 dispatches to the WRONG struct's method via alias bridge
- Freestanding bare->qualified alias bridge resolved a scalar `.to_u32()` to `Color.to_u32`
  (fb_driver) -> fault (cr2=0, bps=0x53535353). Avoid bare conversion-method calls on scalars in
  kernel code; use `as u32` casts (no method dispatch).

## C8. Trait-object dispatch performs an extra dereference (vtable slot treated as ptr-to-ptr)
- `Fat32Core.read_boot_sector+0x18` calling `self._device_sector_size()` through a BlockDevice
  trait object wild-jumps with rip=cr2=0x0001e0ec8148e589 — exactly the callee's first 8 CODE bytes
  (`push rbp; mov rbp,rsp; sub rsp,0x1e0`) interpreted as an address: the dispatch loads function
  ENTRY BYTES instead of calling the entry. 21k+ recovered-fault storm, boot hang pre-framebuffer.
- Mitigation landed: hosted fat32 mount skipped behind marker
  `[vfs-init] hosted fat32 mount skipped: blockdevice-dispatch-codegen-bug` (vfs_boot_init.spl).
  THIS IS NOW THE ONLY REMAINING DISK BLOCKER (apps=0, bitmap font) — fix at seed level.

### C8 investigation addendum (2026-07-17, SEED-CODEGEN lane) — STILL OPEN

Two separate findings from this investigation session. Do not conflate them —
neither the tests nor the boot below credit the second finding as a fix for
this bug.

1. **A real, separate vtable-compaction OOB bug was found and fixed.**
   `emit_vtable_data_objects` (codegen/common_backend.rs) sized and populated
   a trait impl's vtable data blob using `Vec<String>.iter().enumerate()` —
   i.e. by the COUNT of methods that specific impl overrides — while dispatch
   call sites (`lowering_core.rs::find_trait_for_method_on_receiver`) compute
   `slot_offset` from the trait's CANONICAL (whole-trait) declaration order,
   independent of any one impl. A struct implementing a non-contiguous subset
   of a trait's methods (e.g. slots {0, 2} of a 3-slot trait, skipping slot 1)
   got a compacted 2-slot/16-byte blob; dispatching the trait's last method
   (real slot 2, byte offset 16) then read one slot past the end of that
   blob — an out-of-bounds garbage read used as a function pointer. Fixed by
   indexing `MirModule::vtable_impls`'s per-impl method vector by canonical
   slot (`Vec<Option<String>>`, sized `max_implemented_slot + 1`, `None` at
   unoverridden slots) in `mir/function.rs`, `mir/lower/lowering_core.rs`, and
   `codegen/common_backend.rs`. Proven by a Cranelift-JIT-executed repro that
   SIGSEGV'd before the fix and passes after
   (`codegen::local_execution_tests::test_cranelift_jit_vtable_dispatch_partial_impl_compaction`,
   plus a `..._full_impl` control case). A derisk check confirmed the live,
   dynamically-dispatched `RenderBackend` trait's `SoftwareBackend` impl
   overrides all 24 declared methods (no gap), so this fix cannot turn that
   working path into a new null-slot crash.

2. **This fix is NOT C8's cause, and C8 reproduces unchanged.** Static
   analysis of the *actual* crash site — `nm`/`objdump` on a same-tree kernel
   build — shows `NvmeBlockAdapter` implements all 3 `BlockDevice` methods
   with no gap, so its vtable is unaffected by the fix above (byte-identical
   before/after). The call sequence at `_device_sector_size` is a clean
   2-load-then-`call` (object→vtable, vtable→slot 2 at offset 0x10, direct
   `call rax`) — no extra dereference, contrary to this bug's original
   hypothesis. With the fix applied and the vfs skip TEMPORARILY lifted, a
   clean, correctly-scoped, from-scratch own-seed build
   (`--entry-closure --backend cranelift --opt-level=aggressive
   --target x86_64-unknown-none`, 666 files compiled, 0 failed) booted under
   QEMU and reproduced the IDENTICAL fault signature: `cr2=0x0001e0ec8148e589`
   incrementing by 2 per recovered fault (the documented fixed-2-byte RIP
   advance), 29k+ occurrences within ~20s — the same fault storm as
   originally reported. The skip has been reverted to `if true:` (original
   text restored). **C8's actual mechanism is still unidentified and the bug
   remains open** — the extra-dereference hypothesis is now disproven for the
   inspected call site (code and vtable both verified correct there), so the
   real cause is elsewhere in the dispatch chain (possibly upstream of the
   vtable — e.g. how `self.device`'s value reaches the trait-object receiver,
   or something specific to the freestanding/entry-closure/aggressive-opt
   compilation configuration that a hosted JIT build does not reproduce).

   One specific lead was chased and ruled out: a dropped store to the
   module-global `g_adapter` (`var g_adapter: NvmeBlockAdapter = ...`,
   reassigned via `g_adapter = adapter` in
   `_vfs_boot_init_pure_nvme_fat32`) — the same class of bug as C1
   ("module-global initializers never emitted"). `objdump` found zero
   references to `g_adapter`'s data address *inside* that one function, which
   looked suspicious at first, but a whole-binary search
   (`objdump -d -M x86-64 desktop.elf | grep <addr>`) found 5 live
   `movabs $<addr>,%reg` references elsewhere — `g_adapter` is read/written
   in the binary; nothing is silently dropped. **Do not re-chase this lead.**

   The one open, unverified lead worth prioritizing: the constructor's vtable
   stamp uses a **RIP-relative** `lea` (position-independent, confirmed
   correct), but every module-global access (including the `g_adapter`
   `movabs` sites above) uses an **absolute** 64-bit immediate. If this
   freestanding `--entry-closure` image is not loaded at the link-assumed
   base address, every `movabs`-addressed global read/write lands on the
   wrong linear address while every RIP-relative access (like the vtable
   stamp, which is why static analysis of it looks correct) still works —
   which would explain both "the code and vtable are provably correct" and
   "it still faults at runtime." `cr2=0x0001e0ec8148e589` is a canonical-form
   48-bit address, consistent with a mis-based pointer chain rather than a
   random vtable slot. Next investigator: check the freestanding image's
   actual QEMU load address against the link-time base, and/or instrument the
   receiver pointer value itself at the `_device_sector_size` call site in a
   freestanding build, rather than re-deriving it from static analysis.

### C8-RELOC lane (2026-07-17) — relocation hypothesis DISPROVEN, bug re-isolated to trait-field storage

**Relocation/load-base hypothesis: DISPROVEN, flatly.** `readelf -l` on the
freestanding kernel ELF (`examples/09_embedded/simple_os/arch/x86_64/linker.ld`,
base `0x100000`) shows all `PT_LOAD` segments with `VirtAddr == PhysAddr`
(`0x100000`, `0x1007000`, `0x100b000`), and the linker identity-maps the first
1GB. QEMU's `-kernel` multiboot1 loader places `PT_LOAD` segments at their
`p_paddr` verbatim — no relocation, no ASLR, no bootloader-side copy. Load
base equals link base exactly. Every `movabs`-addressed global and every
RIP-relative access resolve to the same linear address; there is no "wrong
base" for either addressing mode to disagree on. **This also means C1
("module-global `val/var X = call()` initializers never emitted") is NOT
explained by a load-base mismatch** — mis-based `movabs` globals was a live
theory for C1 too, but with load base confirmed correct, C1 remains a
separate, still-unexplained defect (the global's init-store code is simply
never emitted/executed, not mis-addressed).

**Static verification of the originally-suspected call site — clean.**
Disassembled `Fat32Core._device_sector_size` (`nogc_async_mut` variant, the
one actually linked; NOT the `nogc_sync_mut` copy) in a fresh from-scratch
build: `and rdi,~7; mov rdi,[rdi]` (load `self.device`) → `and rax,~7; mov
rax,[rax]` (deref to vtable) → `mov rax,[rax+0x10]` (slot 2 = `sector_size`,
matching trait declaration order) → `call rax`. Confirmed the vtable data
blob (`__vtable__NvmeBlockAdapter__for__BlockDevice`) holds the exact correct
3 function-pointer slots (`read_sector`, `write_sector`, `sector_size`,
byte-for-byte matched against fresh `nm` addresses), and confirmed BOTH
`NvmeBlockAdapter` constructors (`new` and `for_identified_namespace_unchecked`,
the latter is what's actually called from `vfs_boot_init.spl`) correctly
stamp `[new_object+0] = &__vtable__NvmeBlockAdapter__for__BlockDevice` via a
RIP-relative `lea`. Construction-site and isolated-call-site statics are
BOTH provably correct — matches the prior lane's finding, independently
re-derived.

**Runtime isolation (the new part): 3 staged serial probes, one rebuild each,
`--entry-closure --backend cranelift --opt-level=aggressive
--target x86_64-unknown-none`, booted under QEMU `-name c8reloc` with an NVMe
drive attached (`build/os/_wk/fat32-font.img`) so the pure-NVMe path is
actually reached (earlier probe attempts without `-drive`/`-device nvme`
silently skipped straight to `no-nvme-or-bad-fs` and never exercised this
code at all — note for the next investigator: `-drive
file=...,if=none,id=nvm,format=raw,snapshot=on -device
nvme,serial=deadbeef,drive=nvm` is REQUIRED to reach this path):**

1. `val bd_probe: BlockDevice = adapter; bd_probe.sector_size()` — concrete
   `NvmeBlockAdapter` local var coerced to `BlockDevice` and dispatched
   immediately at construction, zero composition. **Printed `ss=64`, no
   fault.** Coercion + dispatch on a freshly-constructed object: clean.
2. Same coercion+dispatch through the **module-global** `g_adapter` (after
   `g_adapter = adapter`). **Printed `ss=64`, no fault.** Rules out a
   mis-stored/mis-reloaded module global for this specific value (consistent
   with, and reinforces, the prior lane's "5 live movabs refs" finding for
   `g_adapter`).
3. `g_pure_nvme_root_fat32 = Fat32Core.new(g_adapter)` (this is actually
   `SharedFat32Driver.new(g_adapter)` — `Fat32Core` is aliased via `use
   os.services.fat32.shared_fat32_driver.{SharedFat32Driver as Fat32Core}`
   in `vfs_boot_init.spl`) — printed fine (assignment completes). Then:
   `g_pure_nvme_root_fat32.inner.mounted` (a plain bool field, TWO levels of
   struct field access: `SharedFat32Driver.inner: Fat32Core`, i.e. the REAL
   `std.fs_driver.fat32_core.Fat32Core`) — read correctly (`0`, not a
   nil-deref). Then immediately: `val inner_bd: BlockDevice =
   g_pure_nvme_root_fat32.inner.device; inner_bd.sector_size()` —
   **FAULTED with `rip=cr2=0x0001e0ec8148e589`, byte-identical to the
   original C8 report and to the prior lane's full-boot repro.** This is the
   decisive reproduction: same exact garbage address, isolated to a single
   two-statement probe with no `read_boot_sector`/`mount()` call chain
   involved at all.

**Verdict — mechanism narrowed, NOT yet pinned to storage-vs-read, NOT yet an
exact instruction.** The trait coercion-and-dispatch machinery itself is
proven correct twice (steps 1–2, same underlying `NvmeBlockAdapter` object,
same vtable, no composition). Step 3 proves the receiver chain up to and
including `.inner` is valid (`.inner.mounted` reads `0`, not a nil-deref, so
`self.inner` is a real, correctly-addressed `Fat32Core`) — the fault
localizes specifically to `.inner.device` and the dispatch on it. **What
this A/B does NOT yet distinguish, and the doc previously over-claimed it
did:**

- **Storage-corrupt-at-write vs. chained-read-corrupt-at-read.**
  `g_pure_nvme_root_fat32.inner.device` is itself a two-hop field chain
  (`SharedFat32Driver.inner` then `Fat32Core.device`), so this probe does
  NOT rule out a chained-erased-receiver-read bug (the documented
  `.claude/rules/language.md` landmine) — it only proves `.inner` alone
  reads correctly, not that `.inner.device` read as a *chain* is equivalent
  to a fresh read. The **untested discriminator**: split the two hops —
  `val f = g_pure_nvme_root_fat32.inner; val bd: BlockDevice = f.device;
  bd.sector_size()`. If this still faults with the same `cr2`, the value is
  corrupt at rest (storage-side bug). If it does NOT fault, the bug is in
  the chained/erased read itself, not storage.
- **Nesting depth.** The probe went straight to the doubly-nested
  construction (`SharedFat32Driver(inner: Fat32Core.new(g_adapter), ...)`,
  a constructor call nested inside another struct literal's field
  initializer). The **simpler, untested shape**: `val f =
  Fat32Core.new(g_adapter); val bd: BlockDevice = f.device;
  bd.sector_size()` — single-level `Fat32Core(device: device, ...)`
  struct-literal field store, no outer nesting. If that alone faults, the
  bug is just "trait-typed constructor argument stored into a struct field
  via a struct literal" (a much more common, higher-priority shape to fix)
  and the nesting is irrelevant.

Fix target for the next lane, scoped honestly: something in how a
trait-typed value gets **stored into a struct field via a
constructor/struct-literal argument, and/or read back through a struct
field**, corrupts the vtable-bearing pointer — construction-site statics
(vtable stamp, vtable data) and direct local/global coercion+dispatch are
both proven correct, so the defect is specifically in this
store-then-later-read path. Likely code: seed `StructInit`/field-store and
field-read lowering (`src/compiler_rust/compiler/src/mir/lower/`,
`src/compiler_rust/compiler/src/codegen/`). Run the two discriminator probes
above (cheap, one rebuild each) before touching codegen — they turn "a trait
field stored via a struct literal is corrupt somewhere" into an exact
trigger shape. Not yet narrowed to an exact file:line or single instruction
either way — the enclosing function (`_vfs_boot_init_pure_nvme_fat32`)
compiles to ~31KB of machine code with the actual dispatch as one of many
indirect `call reg` sites and no vtable-address cross-reference visible via
`objdump`/`nm` alone; isolating the exact instruction needs either a minimal
standalone repro compiled outside this function, or seed-side
instrumentation of the `StructInit`/field-store lowering itself.

**Files touched during this investigation, all reverted before finishing:**
temporary serial probes in `src/os/services/vfs/vfs_boot_init.spl` and
`src/lib/nogc_async_mut/fs_driver/fat32_core.spl` (raw-pointer/`mmio_read64`
probes in the latter were themselves a dead end — `unsafe_addr_of` on a
receiver/trait value appears to box through `any` and return a
non-physical-looking address under `-m 2G`, e.g. ~14GB; do not repeat that
approach — use typed dispatch-and-print probes like steps 1-3 above
instead). `vfs_boot_init.spl:374` is confirmed restored to `if true:`
(hosted FAT32 mount stays skipped; C8 is still open, not fixed by this
lane).
