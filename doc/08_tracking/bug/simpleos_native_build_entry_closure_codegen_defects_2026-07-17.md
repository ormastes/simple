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
