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

### C1 root-fix (2026-07-17, C1-GLOBALINIT lane) — LANDED (entry-file case); library-module case was already fixed

Two independent mechanisms turned out to be involved, landed at different
times on 2026-07-17. Neither was previously verified against this doc's
original repro.

1. **Library-module call-initialized globals (this doc's original
   `_browser_default_font_lock` repro shape) were already fixed before this
   lane started**, by `inject_freestanding_module_global_init`
   (`src/compiler_rust/compiler/src/pipeline/native_project/module_global_init.rs`,
   landed 2026-07-17 01:13 UTC, commit `4d3f37e3e9e`) together with the
   linker's `generate_init_caller`
   (`native_project/linker.rs::generate_init_caller`, aggregates every
   `__module_init_*` symbol across all compiled objects into
   `__simple_call_module_inits`) and the freestanding x86_64 boot stub
   (`examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s:319-330`, which
   calls `__simple_call_module_inits` before `spl_start`). Confirmed
   empirically: a library module with `var g = make_thing()` compiles to a
   real `V`-defined global plus a `T __module_init_<mod>_dynamic` function
   containing the assignment, unaffected by anything below.

2. **Entry-file call-initialized globals were a separate, still-open gap,
   now fixed.** `wrap_entry_script_as_main`
   (`native_project/compiler.rs`) runs on every `--entry` `.spl` file with no
   function literally named `main` — the common shape for freestanding OS
   entry points, which define their own boot entry (`fn spl_start():`, as
   `gui_entry_desktop.spl` does) instead. Before this fix, any top-level
   `val`/`var`/`const`/`static` whose initializer was not compile-time
   constant (the restored-but-partial `is_liftable_global_decl`/
   `is_const_global_initializer` check only rescued literal-valued
   declarations) was moved into the body of a *synthetic* `main` function.
   Under freestanding/entry-closure builds that synthetic `main` is dead code
   (real entry is `spl_start`/`_start`, never `main`) — but the bug is worse
   than a missed runtime side effect: `module_pass.rs`'s HIR registration
   only scans *top-level* `module.items`, so a declaration buried inside
   `main`'s body was never registered as a global AT ALL. Any other
   top-level function in the same file referencing that name compiled to a
   dangling `GlobalLoad`/`GlobalStore`.
   - **Empirical repro** (seed native-build,
     `--entry-closure --target x86_64-unknown-none --backend cranelift`):
     entry file defining `spl_start()`, a top-level `var h = local_make()`
     read from `spl_start`. Before fix: **link failure**,
     `undefined symbol: entry_kernel__h_entry_thing` referenced from
     `entry_kernel__spl_start`. After fix: links cleanly;
     `nm` shows `h_entry_thing` as a real defined (`V`) global and
     `spl_start` resolved.
   - **Fix**: `wrap_entry_script_as_main` now takes an `is_freestanding: bool`
     (computed from `effective_target().os` at the call site in
     `compile_file_to_object`, before the wrap runs instead of after). Under
     freestanding targets, *every* top-level `Node::Let`/`Const`/`Static` stays
     lifted at module scope (not just const-foldable ones) — `module_pass.rs`
     then registers a real global for it, and
     `inject_freestanding_module_global_init` (which already ran after this
     transform, previously starved of input for entry files) now sees it and
     synthesizes the runtime-init assignment.
   - **Tests**: new file
     `src/compiler_rust/compiler/src/pipeline/native_project/entry_closure_global_init_tests.rs`
     (4 tests, deterministic AST-level, no target/OnceLock global state
     touched): confirms freestanding keeps both const- and call-initialized
     entry-file globals at module scope; confirms hosted (non-freestanding)
     script-entry behavior is unchanged (regression guard); confirms
     `wrap_entry_script_as_main` + `inject_freestanding_module_global_init`
     chained together actually produce a `__module_init_entry_kernel_dynamic`
     function whose body assigns `h_entry_thing` (closes the "link succeeds
     but nothing ever runs the initializer" gap — link success alone does not
     prove the runtime-init function was generated). All 4 FAIL before this
     fix / PASS after (verified via git-HEAD-content swap, not just code
     reading). Deviated from originally-planned test location
     (`codegen/entry_closure_global_init_tests.rs`) to keep the test beside
     the code it exercises and avoid a merge conflict with a concurrent lane
     appending to `codegen/local_execution_tests.rs`.
   - **Scope note**: `wrap_entry_script_as_main`'s condition calls
     `is_liftable_global_decl`, itself dependent on `is_const_global_initializer`
     — both of these have been silently reverted by same-day `chore(wc):
     session sync` commits at least twice already (see the `1386666fadf`
     "worktree salvage" commit message and the C8 addenda above for the same
     pattern). If reverted again, this fix will fail to compile (not
     silently regress) since `wrap_entry_script_as_main`'s new 2-arg
     signature and the `entry_closure_global_init_tests.rs` module both
     depend on it existing.
   - **Not yet migrated**: the ~75 FSK004 lazy-init workarounds in `src/os/**`
     can in principle be migrated back to plain module-level initializers now
     that both mechanisms are confirmed working, but that migration was
     explicitly out of scope for this lane and was not attempted.
   - **Unverified**: whether the actual `gui_entry_desktop.spl` build (full
     SimpleOS kernel, not the minimal 2-file repro) now boots further/renders
     correctly with this fix — not re-run under QEMU by this lane; the fix is
     verified at the AST-transform and seed-CLI-link level only.

### C8-FIELD lane (2026-07-17) — six-way static elimination, dispatch codegen is CLEAN; reframed to runtime data corruption

Picked up the two untested discriminators the C8-RELOC lane flagged (storage-
vs-chained-read, nesting depth) and ran them, plus several more, across every
compilation pipeline this repo has. **Every one is clean.** This section
documents the elimination and reframes where the bug must actually live.

**Repro fixtures used throughout:** a 3-method trait (`read_x`/`write_x`/
`size_x`, matching `BlockDevice`'s exact 3-method/slot-2 shape) implemented by
one struct, nested two levels deep (`Outer.inner: Middle`, `Middle.device:
Dev`), built via nested struct-literal constructors exactly like
`SharedFat32Driver(inner: Fat32Core.new(device), ...)`, then dispatched via
`o.inner.device.size_x()` in various forms. A 1-method trait was tried first
and discarded — slot offset 0 makes "correct 2-deref dispatch" and "one extra
deref" produce identical bytes (`[rax+0]` vs `[rax]`), so it cannot
discriminate; the 3-method/slot-`0x10` shape is required.

**Six independent negative results, weakest to strongest:**

1. **Hosted Cranelift JIT** (`LocalExecutionManager::cranelift()`, is_pic=true,
   host x86_64-linux). Four new tests added to `local_execution_tests.rs`
   alongside the existing two vtable-dispatch controls:
   `test_cranelift_jit_vtable_dispatch_two_level_single_local_chain` (the
   exact C8-RELOC step-3 shape: `val bd: Dev = o.inner.device; bd.size_x()`),
   `..._two_level_split_hops` (discriminator a: `val mid = o.inner; val bd:
   Dev = mid.device; bd.size_x()`), `..._single_level_no_outer_nest`
   (discriminator b: no outer struct, `Middle` alone), and
   `..._two_level_chained_expr` (`o.inner.device.size_x()` with no
   intermediate local at all). **All four return 99 correctly.** 18/18 in
   `codegen::local_execution_tests`, 18/18 in `seed_regression`.
2. **AOT single-module, freestanding, matched settings**
   (`codegen::cranelift::Codegen::for_target_with_opt_level_and_cpu`,
   `x86_64-unknown-none`, `NativeOptimizationLevel::Aggressive` ->
   `is_pic=false` per `BackendSettings::aot_for_target`, matching the kernel
   build's `--opt-level=aggressive --target x86_64-unknown-none` exactly).
   Disassembled the emitted `.o` directly (`objdump -dr`): dispatch is
   `and rax,~7 ; mov rax,[rax]` (object -> vtable) `; mov rax,[rax+0x10]`
   (vtable+slot2 -> fnptr) `; call rax` — a clean, correctly-offset 2-deref
   sequence. No extra indirection.
3. **The real native-build pipeline, not the Rust API bypass.** Established
   that `native-build`'s actual frontend (discovery, HIR lowering, MIR
   lowering — including the `TraitMethod`/`Unresolved` resolution logic in
   `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` and
   `src/compiler/35.semantics/resolve_strategies.spl`) is the **pure-Simple
   self-hosted driver** (`src/app/cli/native_build_main.spl` +
   `src/compiler/*.spl`), spawned as a worker process by the Rust seed's
   `native-build` subcommand; the Rust codegen crate (`compiler_rust`) only
   supplies the final Cranelift/LLVM emission backend. Tests 1-2 above use
   `compiler_rust`'s OWN Rust-side `hir::lower`/`mir::lower_to_mir`, which is
   a **separate, parallel implementation** from the pipeline that actually
   built the faulting kernel — so they are weaker evidence than tests 3-6,
   which drive the real worker end to end. (Also confirmed independently:
   the currently-deployed `bin/simple` is the Rust-cargo-built seed binary
   itself — `strings` shows `cranelift-entity`/`rand` crate paths and
   `driver/src/seed_warning.rs`'s literal warning text — not a self-hosted
   pure-Simple binary, so `src/compiler_rust` is confirmed to be in the
   live path for the actual kernel-build recipe.)
4. **Cross-module, local var, real pipeline.** Two `.spl` files (struct/trait
   definitions + `build_outer()` constructor in one module, the two-hop
   dispatch in a second module importing the first — mirroring
   `shared_fat32_driver.spl` vs `vfs_boot_init.spl`), built via
   `bin/…/target/bootstrap/simple native-build --entry-closure --backend
   cranelift --opt-level=aggressive --cpu x86-64-v1 --target
   x86_64-unknown-none` (env: `SIMPLE_BOOTSTRAP=1
   SIMPLE_ALLOW_FREESTANDING_STUBS=1`), producing two separate cached `.o`
   files and a linked ELF. Disassembled the LINKED ELF: `build_outer`'s
   writes (`Outer.inner`@0, `Middle.device`@0, `DevC`'s vtable ptr@0, all via
   RIP-relative `lea` for the vtable stamp) agree exactly with
   `run_two_hop_combined`'s reads; final dispatch is the same clean
   `[rax] ; [rax+0x10] ; call` sequence. **This disproves the offset-
   disagreement-across-modules hypothesis directly** (write-side and
   read-side offsets checked byte-for-byte, not inferred).
5. **Cross-module, module-level global, real pipeline.** Same as #4 but the
   outer struct is held in `var g_outer: Outer = build_outer()` at module
   scope and reassigned (`g_outer = build_outer()`), mirroring
   `g_pure_nvme_root_fat32`'s actual shape exactly (this specific variant —
   global storage of the OUTER struct, not just the inner `g_adapter` the
   prior lane checked — was untested until now, and is a real bug class in
   this codebase per C1 "module-global initializers never emitted"). The
   global read/write goes through `movabs` absolute addressing (not
   RIP-relative) as expected; still a clean 2-deref dispatch at the end,
   correct slot offset.
6. **TypeId-collision decoy, real pipeline.** Directly targeted commit
   `8932fcb3a14` ("fix(seed): key vtable selection by struct NAME, not
   per-module TypeId" — landed the night before this lane, fixing a
   cross-struct vtable-data clobber from `HirModule::new()` resetting the
   `TypeId` allocator per module). Added a third module defining an unrelated
   5-method trait/struct (`DecoyTrait`/`DecoyStruct`) that, as the first
   user-defined type in its own module, very plausibly collides on the same
   raw per-module `TypeId` as `DevC` in the C8 fixture module; wired it into
   the same `--entry-closure` closure and called both paths from `main`.
   `nm`/`readelf -sW` on the resulting ELF show two separate, correctly-sized
   vtable data objects (`__vtable__DevC__for__Dev` = 24 bytes/3 slots,
   `__vtable__DecoyStruct__for__DecoyTrait` = 40 bytes/5 slots) with correct
   relocation content (function addresses match `nm` exactly, in declaration
   order) and no cross-contamination; the dispatch site for `DevC` still
   resolves through `DevC`'s own vtable, unaffected by the decoy. **This
   specific already-fixed collision class does not resurface for C8's shape
   either.**

**Reframe (per external review of this elimination — recorded here because
it changes the search space for the next lane):** dispatch is a clean 2-deref
`obj -> [obj]=vtable -> [vtable+0x10]=fnptr -> call` in every build config,
including ones matched to the faulting kernel's exact flags. A wild jump to
the callee's OWN prologue bytes despite clean dispatch code means the
*pointed-to runtime data* is wrong, not the *dispatch instructions* — i.e.
either (a) the live object's field-0 does not actually contain the vtable
data address at runtime (corrupt-at-construction, or overwritten after
construction, or the receiver isn't the object it's assumed to be), or (b)
the vtable data section's bytes are overwritten by the time the dispatch
runs. **Both are runtime corruption, invisible to any static `.o`/ELF
disassembly** — which is exactly why six independent static analyses (three
from the C8-RELOC lane, three more here) all come back clean while the
kernel still faults. Static analysis of this dispatch shape is now
exhausted; further identical-flavor static repros are not expected to add
information.

**Correction to the task's own recipe pointer, discovered en route:**
`scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs` builds
`wm_entry.spl` — this entry file does **not** import `vfs_boot_init` at all
(`grep -rl vfs_boot_init examples/09_embedded/simple_os/arch/x86_64/*.spl`
lists `boot_stage2/3_entry.spl`, `desktop_entry.spl`,
`desktop_import_probe_entry.spl`, `desktop_e2e_entry.spl`,
`fs_exec_general_ring3_entry.spl`, `gui_entry_desktop.spl`, `os_entry.spl`,
`servers_entry.spl`, `shell_serial_entry.spl`, `tools_verify_entry.spl`,
`toolchain_exec_probe_entry.spl`, `toolchain_vfs_probe_entry.spl` — NOT
`wm_entry.spl`). A from-scratch `wm_entry.spl` build (fresh, isolated
`--cache-dir`, `--clean`, `vfs_boot_init.spl:374` toggled to `if false:`)
confirmed this empirically: `nm` shows a legacy lowercase C-style
`_fat32_*`/`nvme_admin_cmd`/`simpleos_nvme_*` driver, zero `NvmeBlockAdapter`
or `sector_size` symbols anywhere in the binary — `wm_entry.spl` boots
through an entirely different, non-pure-Simple FS/NVMe path and cannot
reproduce C8 by construction. `gui_entry_desktop.spl` — the entry named in
C1-C4's own header ("All found on `native-build`... building
`gui_entry_desktop.spl`") and imported by `check-simpleos-x86-64-wm-qemu-
readiness.shs` / `check-simpleos-wm-fullscreen-evidence.shs` / others — is
the correct entry point; it directly imports `vfs_boot_init` via
`os.services.vfs.vfs_init`. **Next lane: use `gui_entry_desktop.spl` as
`--entry`, not `wm_entry.spl`, for any further C8 QEMU work.**

**The decisive static check — DONE, no QEMU needed, and it redirects the
fix locus.** Built `gui_entry_desktop.spl` fresh (isolated `--cache-dir`,
`vfs_boot_init.spl:374` briefly `if false:`, same flags as the kernel
recipe: `--backend cranelift --cpu x86-64-v1 --opt-level=aggressive --mode
dynload --entry-closure --target x86_64-unknown-none`, linked via
`clang --target=x86_64-unknown-elf`; 684 files compiled matching the prior
lane's "666 files" ballpark, confirming this is the same real build).
`nm` now shows `NvmeBlockAdapter`'s full method set including
`services__vfs__vfs_block_adapters__NvmeBlockAdapter_dot_sector_size` at
`0a601232` and `__vtable__NvmeBlockAdapter__for__BlockDevice` at `0a7d04c8`.
Disassembled `sector_size`'s actual prologue:

```
0a601232 <...NvmeBlockAdapter_dot_sector_size>:
 a601232: 55                    push   %rbp
 a601233: 48 89 e5              mov    %rbp,%rsp
 a601236: 48 81 ec 90 00 00 00  sub    $0x90,%rsp
```

**`sub $0x90,%rsp` — a 144-byte frame, NOT `sub rsp,0x1e0` (480 bytes).**
`NvmeBlockAdapter.sector_size()`'s real entry bytes, in *this* build, do not
match the fault value's decoded bytes.

**Correction to this lane's own first-pass check (do not repeat the
mistake):** an initial `grep` for the literal mnemonic text `sub
$0x1e0,%rsp` over `objdump -d`'s decoded output found zero matches and this
doc briefly concluded "no function anywhere has a 480-byte frame" /
"corruption is non-code garbage." **That check was wrong and the conclusion
has been retracted.** `objdump`'s linear/recursive disassembly only prints
`sub $0x1e0,%rsp` at addresses it independently decided were instruction
*boundaries* — the fault value is a candidate *byte offset into anywhere in
`.text`*, not necessarily a boundary objdump's decoder ever visits (and
many functions in this codebase interleave single-byte `movb $imm,(%reg)`
string-literal writes for inlined panic messages, which reliably desyncs
objdump's linear decode for long stretches — confirmed directly: manually
walking `Fat32Core._device_sector_size`'s own disassembly in this exact
684-file build repeatedly hit stray `.byte 0xXX` decode failures from this
exact cause). The correct check is a **raw byte search** of `.text`, not a
text-search of objdump's rendering. Redone properly
(`objcopy -O binary --only-section=.text`, then a byte-string search for
`89 e5 48 81 ec e0 01` — the exact 7 bytes this lane's own earlier
reasoning derived as the byte-for-byte match for `cr2`, read starting 2
bytes into a `push rbp; mov rbp,rsp; sub rsp,0x1e0` prologue): **61
occurrences** in this build's 41.6MB `.text` section. This byte sequence is
common, not absent — `sub rsp,0x1e0` (480-byte frames, likely from the same
inlined-panic-string pattern seen throughout this codebase) is a widely
repeated shape, not a unique fingerprint. Attempting to also manually trace
`_device_sector_size`'s own dispatch instructions to completion (to check
whether *this specific* call site's slot-2 dispatch is clean or corrupted
in this exact 684-file build, as opposed to the differently-built binary
the C8-RELOC lane inspected) hit the same objdump-desync wall — the
function is dominated by multi-hundred-byte inlined error-string
construction, and manually re-deriving true instruction boundaries through
it by hand was not completed in this session.

**Net effect of the correction:** the "zero matches -> non-code garbage,
upstream of vtable selection" claim is **retracted**. The extra-deref
hypothesis (dispatch reads the callee's own code bytes as a pointer) is
**not eliminated** by this check — if anything, the 61-occurrence result
shows it remains entirely plausible in general, since 480-byte frames are
common in this codebase and the true faulting build's actual
`_device_sector_size`/`sector_size` shape at the time of the original
report may well have had one. This lane's six-way *dispatch-instruction*
elimination (clean 2-deref, correct offset, in every isolated
shape/pipeline/module-topology tried) still stands on its own terms — it is
strong evidence the *general* struct-field-trait-dispatch lowering
mechanism is not systematically broken — but it does **not**, on its own,
prove the specific corruption in the real kernel build is "upstream of
vtable selection" rather than "an extra dereference at this one call site
under conditions (register pressure, specific surrounding code, or a
codegen path this lane's minimal fixtures didn't trigger) not reproduced by
this lane's fixtures." Both remain open.

**Recommended next probe, unretracted:** a genuine QEMU boot with the vfs
skip lifted (entry = `gui_entry_desktop.spl`, per the correction above),
instrumented with a **typed runtime print** (not raw-address, which already
failed once via `any`-boxing) at the `_device_sector_size` call site: print
the integer value of the receiver pointer itself and of `*(receiver)` (its
claimed vtable pointer field), and compare both against the static
`__vtable__NvmeBlockAdapter__for__BlockDevice` address from a fresh `nm` of
that exact build. Receiver's field-0 ≠ the static vtable address -> the
object's vtable pointer is corrupt at rest (hunt the store, or the receiver
isn't actually an `NvmeBlockAdapter`) — consistent with "upstream of
dispatch." Field-0 *matches* the static vtable address exactly, yet the
call still lands on a wild address -> the dispatch *instructions themselves*
are doing something wrong specifically at this call site despite this
lane's clean isolated-fixture results (an extra deref, or a slot-offset
miscomputation this lane's fixtures didn't trigger) — consistent with the
original "extra deref" theory being right after all, just not reproducible
in isolation. This single runtime comparison is what actually decides the
fix locus; neither this lane's static work nor any further isolated-shape
repro can substitute for it.

**Files touched during this lane, final state confirmed:**
`src/compiler_rust/compiler/src/codegen/local_execution_tests.rs` (4 new
control tests, kept — permanent regression coverage), `src/os/services/vfs/
vfs_boot_init.spl` (line 374 toggled `if true:` -> `if false:` -> `if true:`
**twice** in this lane — once for the wm_entry.spl false-start, once for the
gui_entry_desktop.spl decisive check — verified via `sed -n '374p'` +
`git diff` = empty after each restoration, never left lifted between steps).
`src/compiler_rust/runtime/build.rs` had 3 pre-existing `jj` conflict
markers (unrelated to C8, from a concurrent lane's merge) blocking ALL
cargo builds in this repo; resolved by keeping both sides' `println!`/
source-list entries (`runtime_hosted_gpu_stubs.c` and `runtime_rocm.c` both
exist on disk and both loops already skip missing files, so keeping both is
safe) — flagged explicitly here since this lane does not commit; a parallel
lane's rebase later converged the working copy back to a clean, matching
`build.rs` on its own, so no action is needed from the coordinator beyond
being aware this happened (this lane's uncommitted edits to
`local_execution_tests.rs` and this doc were also silently reverted once by
the same kind of concurrent sync mid-session and had to be re-applied —
flagging this so the coordinator commits promptly rather than leaving this
lane's output uncommitted). Scratch/one-off repro sources and kernel builds
(including `build/os/simpleos_wm_x86_64_c8check*.elf` and
`build/os/simpleos_desktop_c8check.elf`, both deleted after use) were kept
under the session scratchpad and `build/os/` (gitignored) and are not part
of this repo's tracked state.

### C8-PROBE lane (2026-07-17) — decisive same-boot A/B: fix locus is
### stored-field readback, position/register-pressure RULED OUT

Ran the recommended runtime experiment: instrumented `_vfs_boot_init_pure_
nvme_fat32` (entry = `gui_entry_desktop.spl`, per the earlier lane's entry
correction) with staged serial probes, rebuilt (`--entry-closure --backend
cranelift --cpu x86-64-v1 --opt-level=aggressive --target x86_64-unknown-
none`, isolated `--cache-dir build/os/_wk/c8probe-cache`, 672 files then 666
cached across iterations, 0 failed each time) and booted 4 times under QEMU
`-name c8probe` with the NVMe drive attached
(`build/os/_wk/fat32-font.img`), toggling `vfs_boot_init.spl:374` to
`if false:` for the duration. Two real findings, one retraction of this
lane's own first-pass reasoning.

**Retraction #0 (methodology): `unsafe_addr_of()` on a concrete-class value
passed through an `any`-typed extern parameter does NOT return the live
object's address.** First attempt followed the doc's suggested raw-
pointer-chase (`extern fn unsafe_addr_of(ref: any) -> u64` +
`extern`-avoided `mmio_read64` reads, masked `& 0xFFFFFFFFFFFFFFF8` per the
disassembled `and reg,~7` pattern) on `adapter` (a concrete
`NvmeBlockAdapter` local, not a trait value — believed safe per the prior
C8-RELOC lane's narrower warning, which only flagged trait-typed values).
Result: `unsafe_addr_of(adapter) & mask` then `mmio_read64(that_addr)`
reported `adapter_vtable=0` — implying a corrupt/missing vtable stamp.
**In the same boot, at the same moment, a BEHAVIORAL dispatch on the exact
same object** (`val bd_early: BlockDevice = adapter;
bd_early.sector_size()`) **returned `ss_early=64` with no fault.** A live
object cannot have both a null vtable pointer (raw read) and a working
dispatch (behavioral call) — the raw-pointer method is reading the wrong
memory (almost certainly an ephemeral copy/box made when lowering the
`any`-typed argument, not the live object), not real corruption. This
extends the C8-RELOC lane's warning: `unsafe_addr_of` is unreliable for
*any* value crossing an `any`-typed argument boundary, concrete class or
trait, not just trait values. **Do not use `unsafe_addr_of` for pointer-
chase probing in this codegen; use behavioral dispatch-and-print instead**
(as done for the rest of this lane, and as the C8-RELOC lane's own
steps 1-3 already did).

**Finding #1: exact-signature reproduction via a 3-statement minimal
behavioral trigger.** Switched to behavioral probes only. Right after
`g_pure_nvme_root_fat32 = Fat32Core.new(g_adapter)` (late in the function —
after grant/init/transfer-evidence/lease/bounce-buffer/DMA/boot-sector-read/
direct-FAT32-scalar-mount/version-probe/exec-probe code has already run),
added:
```
val c8p2_mid = g_pure_nvme_root_fat32.inner
val c8p2_bd: BlockDevice = c8p2_mid.device
val c8p2_ss = c8p2_bd.sector_size()
serial_println("[c8probe2] ss_late_split_hop={c8p2_ss}")
```
This is the split-hop shape (C8-RELOC's storage-vs-chained-read
discriminator) — deliberately NOT the single chained expression
`g_pure_nvme_root_fat32.inner.device.sector_size()`, to also test that
discriminator. **Result: faulted before the print ever ran, with
`rip=cr2=0x0001e0ec8148e589` — byte-identical to the original report and
every prior reproduction.** 34,370 recovered-fault storm entries, `cr2`
incrementing by 2 per fault (the documented fixed-2-byte RIP-advance
recovery), `ra=0x000000000a5ed46c` constant across every frame (the return
address one call-frame up, in `vfs_boot_init`'s call to
`_vfs_boot_init_pure_nvme_fat32` — the crude single-level backtrace cannot
localize further inside that ~31KB function; re-attempting a manual
disassembly walk to the exact faulting instruction was not repeated here
since two prior lanes already hit the same objdump-desync wall on this
function). **This also answers C8-RELOC's storage-vs-chained-read
discriminator: the SPLIT-hop form faults identically to the combined form,
so "chained/erased expression syntax" is not the mechanism** — ruling out
the specific "chained methods on erased receivers" landmine
(`.claude/rules/language.md`) as C8's cause.

**Finding #2 (the earned verdict): a same-position discriminator rules out
position/register-pressure and isolates the trigger to stored-field
readback.** This lane's first read of finding #1 (early bare-local dispatch
clean, late two-hop-through-field dispatch faults) was that LATE POSITION
in a large, register-heavy function was the trigger — plausible, and it
would have matched the doc's own standing hypothesis ("conditions
(register pressure, specific surrounding code...) not reproduced by this
lane's fixtures"). **This was wrong, and a cheap same-boot control
disproves it.** Immediately before the split-hop probe above, at the
IDENTICAL late position (same register pressure, same surrounding code,
same call depth), added two more behavioral dispatches:
```
val c8p2_direct_local: BlockDevice = adapter
serial_println("[c8probe2] ss_direct_local={c8p2_direct_local.sector_size()}")
val c8p2_direct_global: BlockDevice = g_adapter
serial_println("[c8probe2] ss_direct_global={c8p2_direct_global.sector_size()}")
```
**Both printed cleanly — `ss_direct_local=64`, `ss_direct_global=64`, no
fault — immediately followed by the split-hop probe faulting with the
identical `cr2=0x0001e0ec8148e589` signature, in the same boot, same
position.** Position and register pressure are held constant across all
three dispatches; the only thing that differs is *provenance*: `adapter`
and `g_adapter` are bare local/global values, never stored into a struct
field, while `g_pure_nvme_root_fat32.inner.device` is a value that passed
through `Fat32Core.new(g_adapter)` → nested struct-literal field store
(`SharedFat32Driver.inner: Fat32Core`, `Fat32Core.device: BlockDevice`) →
field read-back. **Verdict: the fix locus is trait-typed struct-field
store/read lowering specifically for the real `Fat32Core`/
`SharedFat32Driver` construction shape** — not dispatch/call-site codegen
in general (direct dispatch is clean, always, everywhere this lane and
prior lanes tested it), not chained-vs-split expression syntax (both
fault), not position/register-pressure (both hold constant across the
pass/fail boundary), and — per the early-construction calibration above
(`ss_early=64` on `adapter` immediately after construction, before any
intervening boot code) — not simple storage-corrupt-at-rest from unrelated
later code either, since the object that fails (`g_pure_nvme_root_fat32`)
is itself constructed fresh, late, from the very same `adapter`/`g_adapter`
that dispatch cleanly at that same late point.

**Why C8-FIELD's synthetic fixtures (6 pipelines, all clean) didn't catch
this — one CONFIRMED gap, one untested hypothesis, do not conflate them.**

*Confirmed: the fixture those four "two_level"/"single_level" tests share
(`C8_FIELD_FIXTURE_PREFIX`, `local_execution_tests.rs:250-265`) declares a
trait with a SINGLE method, `size_x`, at slot 0* — not the 3-method
`read_x`/`write_x`/`size_x` shape at slot `0x10` the C8-FIELD doc text
itself says is "required" ("A 1-method trait was tried first and
discarded — slot offset 0 makes 'correct 2-deref dispatch' and 'one extra
deref' produce identical bytes... the 3-method/slot-`0x10` shape is
required," line ~294 above). The two claims disagree: the doc's prose says
3-method/slot-0x10 was used "throughout," but the actual constant in the
test file that backs the four most-analogous tests (including
`two_level_split_hops`, the exact discriminator this lane re-ran live) is
1-method/slot-0. At slot 0, `[rax+0]` (correct) and a hypothetical
extra-deref read at the same offset are byte-identical — **the fixture
those four tests use cannot discriminate the extra-deref hypothesis at
all, independent of field count.** This is a concrete, fixable defect in
the existing test harness, separate from and prior to any new enrichment.

*Untested hypothesis: field count/type mix.* The real `Fat32Core` has ~24
fields after `device` (mixed `u32`/`bool`/array/`[u8]`/`[[u8]]` types,
several leading underscore-prefixed cache fields), and `SharedFat32Driver`
wraps it inside another multi-field struct (`inner`, `handles:
[SharedFileHandle]`, `handle_ids: [u64]`, `next_handle: u64`, `mounted:
bool`) — versus the synthetic fixture's 2-3 total fields. This lane
believes field count/mix is *also* likely relevant (a 1-field struct has
no layout/spill pressure a 24-field one does), but this was **not tested**
this session — say so plainly rather than asserting it.

**Recommended next step for whoever picks this up:** fix the fixture to
use a proper 3-method/slot-`0x10` trait (matching `BlockDevice` exactly, as
the doc's own prose already specifies) AND separately enrich field
count/type mix toward `Fat32Core`'s actual shape, as two independent axes —
run the slot-0x10 fix alone first (cheapest, fastest, and directly
addresses a real harness defect regardless of the field-count question) to
see if it alone flips any of the four tests red before conflating it with
field-count enrichment. This is a fast (seconds, not QEMU-boot-minutes),
Rust-side seed-level repro search — this lane did not attempt it due to
time; it is the natural continuation of C8-FIELD's existing 4-test harness
in `src/compiler_rust/compiler/src/codegen/local_execution_tests.rs` and
`c8_nested_field_dispatch_tests.rs` per the task brief, once a repro shape
is found. No fix was attempted this session without that fast feedback
loop — editing seed struct-literal/field lowering on a hypothesis with a
~4-minute rebuild+boot verification cycle risked breaking the already-
correct `RenderBackend`/24-slot dispatch path for no confirmed gain, and a
parallel worktree lane was already mid-`cargo test` on this same crate
when this lane finished, so no cargo build was started here either.

**Static reference addresses for this exact build** (`build/os/_wk/
c8probe_desktop.elf`, gitignored scratch, deleted after use): `nm` showed
`__vtable__NvmeBlockAdapter__for__BlockDevice` at `0a7bc4c8`
(175883464 decimal), `NvmeBlockAdapter_dot_sector_size` at `0a5ec0aa`
(173981866 decimal) — both stable across every rebuild in this lane (only
the instrumented function's own bytes changed between iterations).

**Files touched, final state confirmed:** `src/os/services/vfs/
vfs_boot_init.spl` — all `c8p0_`/`c8p2_`/`c8probe`-prefixed instrumentation
and the `extern fn unsafe_addr_of` declaration added by this lane were
stripped after the final boot; `vfs_boot_init.spl:374` toggled `if true:`
-> `if false:` -> `if true:` (restored, verified via `sed -n '374p'` and an
empty `git diff` on the file). No files outside `src/os/services/vfs/
vfs_boot_init.spl` were edited by this lane. Scratch kernel builds, cache
dirs, and serial logs live under `build/os/_wk/` (gitignored); serial logs
gzipped, kernel ELF and native-build cache dir removed after use.

### C8-FIX lane (2026-07-17) — harness fixed, root cause FOUND and CONFIRMED
### at the real fault site; deployed seed is 6 days stale; full kernel
### re-verification blocked by an unrelated build-plumbing gap
**1. Harness defect fixed (task step 1).** `C8_FIELD_FIXTURE_PREFIX`
(`src/compiler_rust/compiler/src/codegen/local_execution_tests.rs`) was
widened from the flawed 1-method/slot-0 trait (`size_x` only — provably
unable to discriminate the extra-deref hypothesis, per the C8-PROBE lane's
"Confirmed" gap) to the exact 3-method/slot-`0x10` `BlockDevice` shape
(`read_x`/`write_x`/`size_x`, `size_x` returns 64 mirroring the real
kernel's `sector_size()` value). All 4 existing tests updated
(`result==99` → `result==64`) and re-verified green. **New, genuinely
untested axis added and executed:** three factory-return-by-value tests
(`test_cranelift_jit_vtable_dispatch_factory_single_level`,
`..._factory_two_level`, `..._factory_module_global`) — every prior
*executed* test in this bug's history built the trait-bearing struct via an
inline struct literal in the same function that dispatches on it; the real
kernel path goes through `static fn new(...)` factories
(`Fat32Core.new(device)` / `SharedFat32Driver.new(device)`) that construct
and return the struct BY VALUE across a call boundary, including into a
module-global. **Full corrected matrix (7 tests) is GREEN under the hosted
Cranelift JIT** (`cargo test -p simple-compiler --lib
codegen::local_execution_tests -- vtable_dispatch`, 18/18 including the 4
control tests) — hosted JIT is_pic=true stays clean for every shape tried,
consistent with every prior lane's finding at this tier. Kept as permanent
regression coverage.
**2. Executed (not just disassembled) AOT-freestanding reproduction.**
Built minimal standalone probe kernels via the REAL `native-build` pipeline
(`--entry-closure --backend cranelift --cpu x86-64-v1
--opt-level=aggressive --target x86_64-unknown-none`, i.e. is_pic=false,
matching the faulting kernel's exact flags) under
`examples/09_embedded/simple_os/arch/x86_64/` (disposable scratch,
deleted after use), booted under QEMU with `-kernel` (no NVMe drive
needed — self-contained, never touched vfs code or `vfs_boot_init.spl`):
- **Single-file, enriched fixture** (3-method trait, factory-return at TWO
  levels, module-global reassignment, split-hop read, ~20-field
  `Middle`/`Outer` structs mirroring `Fat32Core`'s field-count/type-mix,
  simulated DMA/bounce-buffer traffic before dispatch) — **booted clean,
  `ss_split_hop=64`, no fault.** First-ever *executed* (not disassembled)
  result at the exact matched AOT/freestanding tier with a corrected+
  enriched fixture; extends the negative-result frontier past every prior
  lane's static-only AOT check.
- **Two-file cross-module variant** (`Dev` trait + `DevC` impl in one
  module, dispatch in another, importing via `use lib_module.{Dev, DevC}`)
  — **FAULTED**, byte-identical signature to the original C8 report:
  `FAULT @ 0x0000000008057e05`, incrementing storm, decoded as the
  fixed-2-byte-RIP-advance recovery loop. Reproduced with BOTH a
  cross-module `static fn new()` factory call and a bare cross-module
  struct literal — factory indirection is not required, plain cross-module
  trait dispatch alone reproduces it. Cleanest, smallest repro this bug
  has had: 2 files, ~40 lines total, no kernel, no disk, no vfs code.
**3. Root cause, pinned via disassembly + a pre-existing debug hook.**
Disassembling the fault site showed NOT a vtable load but a call to
`rt_eprintln_str` printing the literal string
`"...backend_method_dispatch_sigsegv_2026-07-1x..."` immediately followed
by a `ud2` trap and `int3` padding. Grepping the seed for that string found
it hardcoded in `compile_method_call_virtual`
(`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1373`):
when the MIR's `vtable_slot` equals the sentinel
`DUCK_DISPATCH_UNSUPPORTED_SLOT` (`u32::MAX`,
`src/compiler_rust/compiler/src/mir/mod.rs:45`), codegen deliberately
emits a diagnostic print + trap instead of a real dispatch — a **known,
intentional** guard from an unrelated 2026-07-02 bug
(`jit_game2d_backend_method_dispatch_sigsegv_2026-07-02`, comment at
`lowering_core.rs:944`), meant only for genuinely duck-typed traits with no
`impl` anywhere. The sentinel is produced in exactly one place:
`find_trait_for_method_on_receiver`
(`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:946-1008`),
whose `slot_for` closure calls `trait_is_implemented(trait_name)` →
`self.dependency_graph.get_implementations(trait_name)`. Using the
**pre-existing** `SIMPLE_DEBUG_METHOD_DISPATCH=1` env hook (already wired
in `lowering_expr_method.rs`, no code change needed to observe it) on the
minimal 2-file repro: `'size_x' lowered as virtual trait call at slot
4294967295` — i.e. `DevC` genuinely implements `Dev` but the compiler's own
dependency graph reports no implementation, misfiring the duck-typed
sentinel guard for a real, present, cross-module impl.
The `ud2` trap then gets treated as just another recoverable event by the
freestanding fault-recovery handler (both `_rich_fault_entry` and crt0's
default handler do a blind "RIP += 2, iretq" on ANY of the 256 IDT
vectors — see the C8-RELOC/C8-PROBE addenda above), so execution resumes 2
bytes into the `ud2`+`int3` padding and free-runs into whatever adjacent
code/rodata follows — exactly why every original C8 report and every prior
lane's repro decoded as "a wild jump reading a callee's own prologue bytes
as an address": that is just where the RIP+=2 walk happened to land in
each specific binary layout, not a property of the trap itself.
**Flagged, not fixed this lane** (separate, real latent defect): the
fault-recovery handler treating an intentional, compiler-emitted `#UD`
trap identically to a page fault is itself wrong, and is *why* every one
of the four C8 investigation lanes chased vtable/pointer-corruption
theories instead of the actual cause — a `ud2` should terminate/park, not
"recover." Worth its own bug entry; out of scope to fix here.
**4. Identity to C8's real fault site — CONFIRMED, not inferred.** The
storm signature alone is non-discriminating (ANY unrecovered trap produces
an identical-looking RIP+=2 walk), and two prior lanes (C8-FIELD item 4,
C8-RELOC) disassembled clean `[rax];[rax+0x10];call` sequences at
cross-module and at the real `_device_sector_size` site respectively — the
opposite of a `ud2`. To resolve this directly rather than relying on
signature similarity: ran the REAL entry point
(`gui_entry_desktop.spl`, full 666-file kernel, same
`--entry-closure --backend cranelift --cpu x86-64-v1
--opt-level=aggressive --target x86_64-unknown-none` flags) through
`native-build` with `SIMPLE_DEBUG_METHOD_DISPATCH=1` (no QEMU needed — the
trace is emitted at MIR-lowering time, before codegen/link) and grepped
the build log for `sector_size`:
- **Stale deployed seed** (`bin/simple`, dated 2026-07-11): `[MIR-METHOD-
  DISPATCH] 'sector_size' lowered as virtual trait call at slot
  4294967295` — the REAL `Fat32Core._device_sector_size` call site
  (confirmed by the adjacent `[CODEGEN-METHOD-STATIC] in
  'Fat32Core.read_boot_sector' func_name='Fat32Core._device_sector_size'`
  trace line — this is literally the call site named in the original C8
  report, "`Fat32Core.read_boot_sector+0x18` calling
  `self._device_sector_size()`") **hits the exact same sentinel as the
  synthetic repro.** Identity confirmed directly, not by signature
  resemblance.
- **Fresh HEAD** (`src/compiler_rust/target/bootstrap/simple`, built this
  lane via `cargo build --profile bootstrap`): the identical trace line
  now reads `'sector_size' lowered as virtual trait call at slot 2` — a
  real, correct vtable slot.
This reconciles the apparent conflict with C8-FIELD/C8-RELOC's clean
disassembly: those lanes' "clean 2-deref dispatch" observations are
real and correct — for whatever binary/commit they happened to build
with at the time (both dated within the window where the underlying
`ca1e18c1744`/`b843353b50e` dependency-graph mechanism was already
fixed or not yet broken) — while the actual production kernel's
`desktop.elf` was built with the stale seed, which sentinels. C8 was
never one single consistently-reproducing shape; it depends on which
`simple` binary compiled the kernel, which is exactly the kind of
non-obvious variable none of the four lanes controlled for.
**5. The dispatch-resolution defect is ALREADY FIXED in current HEAD —
the deployed seed is 6 days stale, this is confirmed at both the
synthetic-repro AND the real-kernel-entry-point level (§4).**
`bin/simple` (`bin/release/x86_64-unknown-linux-gnu/simple`, the binary
every prior C8 lane and this lane's early probes ran) is dated
**2026-07-11 08:52**, six days behind HEAD. Nearest relevant landed
history: `b843353b50e` ("fix(seed): scope trait-impl virtualization to
local impls", 2026-07-16, ancestor of HEAD) reworked
`find_trait_for_method_on_receiver` following a bisect on an unrelated
fb-init regression from `ca1e18c1744`, which is where the project-wide
`dependency_graph`/`imports.trait_impls` cross-module mechanism this bug
depends on was introduced in the first place. **Not pinned to a single
commit** — `b843353b50e`'s own diff targets the "concrete receiver, no
local impl" branch (lines 987-1006), not the "receiver typed as the trait
itself / unknown receiver" branches (964-978) that this specific repro's
trace actually takes, so the exact fixing change may be `ca1e18c1744`
itself (adding the mechanism) rather than `b843353b50e` (narrowing it) —
`git bisect` the stale-seed-vs-HEAD slot value directly if the exact
commit matters (cheap: `SIMPLE_DEBUG_METHOD_DISPATCH=1`, no QEMU, no
rebuild needed since the two binaries already exist in this repo).
**6. Full kernel re-verification (task step 4: lift `vfs_boot_init.spl:
374`, boot with NVMe, confirm the fault storm is gone) NOT completed this
lane — blocked by an unrelated build-plumbing gap, not by C8 itself.**
Every ad-hoc `cargo build` of the driver from current HEAD (both
`--release` and `--profile bootstrap`, with and without
`SIMPLE_RUNTIME_PATH` set) linked freestanding kernels with the ~4000
`auto_stubs.c`/`primitives.c` runtime stub symbols (including
`rt_eprintln_str` itself) silently absent — confirmed via `nm` symbol-
count comparison (236 symbols / 45 KB vs the properly-deployed seed's
4148 symbols / 563 KB for an equivalent tiny probe) BEFORE booting it, so
no fault result from that binary was trusted or reported as a dispatch
result. This is a link/build-plumbing artifact, not a second dispatch
bug; root-causing it was out of scope for this lane. It does NOT affect
finding §4 above, which used the MIR-lowering debug trace (emitted before
codegen/link) rather than a booted binary. **`vfs_boot_init.spl:374` was
never touched this lane** — `git diff` on that file empty throughout,
re-verified multiple times including after a mid-task resume.
**Handoff for the next lane:** redeploy `bin/simple` from current HEAD via
the repo's real bootstrap/deploy recipe
(`scripts/bootstrap/bootstrap-from-scratch.sh` or the documented stage-2/
redeploy recipe — NOT ad-hoc `cargo build`), confirm the deployed binary's
`sector_size` trace now reads a real slot (same one-line
`SIMPLE_DEBUG_METHOD_DISPATCH=1` + grep check used in §4, ~90s, no QEMU),
then proceed to task step 4: lift the vfs skip, boot with NVMe attached,
confirm the real kernel's fault storm is gone, restore the skip.
**Suite counts (this lane, current HEAD, hosted `cargo test`):**
`codegen::` (`cargo test -p simple-compiler --lib codegen::`): 772 passed,
142 failed, 2382 filtered — all 142 failures are in GPU/SIMD/actor/
coverage-probe/VHDL codegen tests, zero overlap with `vtable_dispatch` or
any test this lane touched; appear pre-existing and unrelated (not
investigated further, out of scope). `seed_regression` (`cargo test -p
simple-compiler --lib seed_regression`): **18 passed, 0 failed.**
`codegen::local_execution_tests -- vtable_dispatch`: **18 passed, 0
failed** (4 corrected + 3 new factory-return + existing controls).
**Files touched, final state confirmed:**
`src/compiler_rust/compiler/src/codegen/local_execution_tests.rs` — kept
(fixture fix + 3 new factory-return tests, permanent regression coverage).
`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs` and
`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs` — temporary
debug `eprintln!`s added and removed via `git checkout --`; `git diff`
re-verified empty of any `C8FIX-DEBUG` marker (the latter file separately
gained an unrelated `mod entry_closure_global_init_tests;` line from a
concurrent lane's sync during this lane's work — not this lane's change,
left alone). Four scratch files under `examples/09_embedded/simple_os/
arch/x86_64/` (`c8fix_probe_entry.spl`, `c8fix_probe_lib.spl`,
`c8fix_probe_caller.spl`, plus intermediate variants overwritten in
place) — all deleted after use, confirmed absent. `src/os/services/vfs/
vfs_boot_init.spl` — not edited by this lane at all; `git diff` empty,
`sed -n '374p'` shows `if true:`. Scratch kernel builds, cache dirs
(`build/os/_wk/c8fix-cache*`, `build/os/_wk/c8fix-realcheck*`), and serial/
build logs under `build/os/_wk/` (gitignored) — left in place for the next
lane's convenience; not committed, gitignored. **Note for the coordinator:**
this addendum was clobbered once mid-session by a concurrent working-copy
sync (the file reverted to its pre-lane 713-line state while this lane's
other edits survived) and was re-applied; commit this file promptly to
avoid a second loss.

### C8-CLOSE lane (2026-07-17) — ud2-recovery hardened; full-kernel
### re-verification run with the fresh seed; C8's boot storm is CONFIRMED
### **NOT resolved** — the dispatch-sentinel fix was necessary but not
### sufficient, a second, still-unidentified runtime defect reproduces the
### byte-identical storm

**Task 1 — the latent ud2-recovery defect is fixed (pure-Simple decision,
minimal asm wiring).** The freestanding fault-recovery ISR
(`_rich_fault_entry`, `examples/09_embedded/simple_os/arch/x86_64/boot/
baremetal_stubs.c:15177-15303`) used to blindly "RIP += 2, iretq" for ANY
kernel-mode (CPL=0), no-error-code vector — including #UD (vector 6). #UD
never pushes an error code, so it is the *only* vector that can land on
that path. A `ud2` (opcode `0x0F 0x0B`) is always an INTENTIONAL trap (e.g.
the compiler's duck-dispatch-sentinel guard in
`compile_method_call_virtual`, `closures_structs.rs:1373`) and must never
be "recovered" — see the C8-FIX lane's item 3 above for why this exact
defect is what turned every honest sentinel trap into a wild-jump storm
throughout this bug's history.

Fix, at `baremetal_stubs.c`'s no-error-code recovery label (`"3:"`,
previously just `addq $2,(%rsp); movq $0x3,%rax; iretq`): before
recovering, read the 2 bytes at the faulting RIP (`movq 16(%rsp),%rax`
after two scratch `pushq`s; `movzwl (%rax),%ecx`) and compare against
`0x0B0F` (the `ud2` opcode as a little-endian u16). `popq` does not touch
EFLAGS, so the scratch registers are restored to their exact fault-time
values *after* the compare and the branch is taken on the still-live ZF —
zero risk of corrupting the interrupted context's registers on the
non-ud2 (unchanged, still-recovering) path. On a match, control passes to
a new label that calls a new pure-Simple function,
`spl_x86_on_kernel_ud2_fault(rip: u64)`
(`src/os/kernel/arch/x86_64/interrupt.spl:367-397`, exported
`@export("C", name: "spl_x86_on_kernel_ud2_fault")`, mirroring the
existing ring-3 `spl_x86_on_user_fault` pattern exactly), which prints a
`FATAL: kernel #UD (ud2) trap at rip=... vector=6 (#UD)` diagnostic to
COM1; the ISR then `cli`/`hlt`-loops and **never iretqs back into the
trap**. All other no-error-code vectors (#DE, #BP, #OF, ...) and the
separate errcode-present kernel-CPL0 path (used by the legitimate W^X
probe, `rt_harden_text_write_trap_probe` in `crt0.s`) are untouched —
confirmed by inspection, the edited block is the sole change.

**Test:** no cheap hosted regression test exists for this — the fix lives
inside a `__attribute__((naked))` ISR stub that can only be exercised by an
actual CPU trap under a freestanding boot; there is no fault-injection
harness for `_rich_fault_entry` under `test/`. Reported honestly per the
task's own allowance rather than adding a source-grep test that would
assert nothing behavioral. The QEMU boot in this lane IS the exercise (see
below) — the fix is proven *inert-but-correct*: it never fired (0
occurrences of the new `FATAL: kernel #UD` marker across a 130s boot with
~69762 recovered faults), which is the CORRECT outcome given item 2 below
(the live crash is not a literal `ud2`), and the code path itself was
verified via disassembly-level manual trace (advisor-reviewed: offset
math, opcode encoding, and the pop-then-branch-on-stale-ZF register
discipline all check out).

**Task 2 — fresh seed built, identity check PASSES, ELF is well-formed,
but the full boot storm reproduces byte-identical to history.**

1. **Fresh seed:** rebuilt via the documented recipe
   (`cargo build --manifest-path src/compiler_rust/Cargo.toml --profile
   bootstrap -p simple-driver`, ~6m46s, exit 0, 0 errors) from current HEAD
   (`f06e5829e1d2`, both `ca1e18c1744` and `b843353b50e` confirmed
   ancestors via `git merge-base --is-ancestor`). Output:
   `src/compiler_rust/target/bootstrap/simple` (27.8 MB, built 08:37 UTC).
   **Not copied to `bin/` — deployment stays user-gated.**
2. **Identity check (link-free, no QEMU):** `SIMPLE_DEBUG_METHOD_DISPATCH=1`
   native-build of `gui_entry_desktop.spl` with the fresh seed. Grep for
   `sector_size`: `'sector_size' lowered as virtual trait call at slot 2` —
   confirmed real slot, not the `4294967295` duck-dispatch sentinel. Grepped
   the **entire** build log (not just `sector_size`) for the sentinel value
   `4294967295`: **zero occurrences, anywhere** — the duck-dispatch-sentinel
   mechanism the C8-FIX lane diagnosed is definitively absent from this
   build, at every call site, not just the one named in the original report.
3. **ELF sanity (the build-plumbing wall the C8-FIX lane hit):** using the
   *production* recipe (`--source build/os/generated --source "$ENTRY"
   --entry-closure --entry "$ENTRY" ... --cache-dir ...`, `SIMPLE_BOOTSTRAP=1
   SIMPLE_LIB=$ROOT_DIR/src SIMPLE_OS_LOG_MODE=off
   SIMPLE_ALLOW_FREESTANDING_STUBS=1`, matching
   `check-simpleos-wm-fullscreen-evidence.shs` exactly rather than the
   task's abbreviated flag list, specifically to avoid reproducing that
   wall) instead of an ad-hoc `cargo build`-adjacent recipe: `Build complete:
   655 compiled, 0 cached, 0 failed`, ELF linked at 16141 KB, **`nm | wc -l`
   = 7212** (well above the ~4000+ healthy threshold, nowhere near the
   ~236-symbol malformed case). Both new fault-handler symbols resolved and
   mirror each other exactly: `spl_x86_on_kernel_ud2_fault` /
   `spl_x86_on_user_fault` both present as `T` (defined, text section) under
   both their mangled (`os__kernel__arch__x86_64__interrupt__...`) and bare
   exported names. **The build-plumbing wall from the C8-FIX lane is not
   reproduced this lane** — this was the production recipe, not an ad-hoc
   one.
4. **Lifted `vfs_boot_init.spl:374`** (`if true:` → `if false:`), rebuilt
   (cache hit 649/655, only the 6 files touched by the one-line change
   recompiled; ELF byte-size identical, `nm` count identical — confirms the
   cache reuse did not silently serve stale dispatch codegen from before the
   fix). Booted under `qemu-system-x86_64 -name c8close` (q35/qemu64/2G,
   `-display none -no-reboot`, NVMe attached via `-drive
   file=build/os/_wk/fat32-font.img,if=none,id=nvm,format=raw,snapshot=on
   -device nvme,serial=deadbeef,drive=nvm`, serial to file), bounded to 130s
   via `timeout 130`.
5. **Result: the fault storm reproduced, byte-identical to every prior C8
   report.** `cr2=0x0001e0ec8148e589` is the very **first** fault of the
   entire boot (immediately after `[vfs-init] scalar scratch read ok
   cluster=3962`, the last live log line before the storm — no earlier,
   unrelated fault precedes it), then increments by exactly `+2` per
   recovered fault for **69762 occurrences** across the 130s window (serial
   log: 697700 lines, 21.7 MB, gzipped to 406 KB at
   `build/os/_wkc8close/serial.log.gz`). The new Task-1 `FATAL: kernel #UD`
   marker **never fired** (0 occurrences) — this specific wild-jump target
   is confirmed NOT a literal `ud2` opcode (the byte-check at that RIP found
   no match), so the storm is going through the *other*, deliberately
   untouched kernel-CPL0 no-error-code recovery path. The backtrace's return
   address is **constant across all 69762 iterations**:
   `[bt] ra=0x0000000008958d0d`. Resolved via `objdump -d -M x86-64` against
   `build/os/_wkc8close/desktop.elf`: this is the instruction immediately
   after `call 89587d2
   <lib__nogc_async_mut__fs_driver__fat32_core__Fat32Core_dot__device_sector_size>`
   inside `Fat32Core.read_boot_sector` — **the exact same call site named in
   the original C8 report** ("`Fat32Core.read_boot_sector+0x18` calling
   `self._device_sector_size()`"). Disassembly of `_device_sector_size`
   itself shows a `self`-tag guard (`and $0xfffffffffffffff8,%rsi; test
   %rsi,%rsi; jne ...`) followed by an inline, byte-at-a-time stack string
   build (`r,u,n,t,i,m,e, ,e,r,r,o,r,:, ,...` — "runtime error: ...") — a
   *different* codegen pattern than the previously-diagnosed duck-dispatch
   sentinel's single `rt_eprintln_str` call + `ud2`, not yet fully traced
   past this point (out of scope for this lane to finish reverse-engineering
   — the exact instruction that computes/jumps to `0x0001e0ec8148e589` was
   not located; the wild target address is far outside the 16 MB ELF's
   range and matches no symbol, consistent with a garbage vtable-slot value
   or corrupted trait-object field read at runtime rather than a
   MIR-lowering/codegen defect).
6. **Conclusion — C8 is NOT closed.** The C8-FIX lane's diagnosis (MIR
   duck-dispatch-sentinel → `ud2` → blind recovery → wild jump) is real,
   confirmed fixed (items 2-3 above), and worth keeping — but it is **not
   the full story**. A second, still-unidentified defect reproduces the
   textually-identical crash signature (same call site, same exact `cr2`
   base address, same +2 walk pattern) even with the sentinel mechanism
   completely absent from the build. This is consistent with the C8-FIELD
   lane's earlier "dispatch codegen is CLEAN; reframed to runtime data
   corruption" hypothesis (see that lane's section above) — the most likely
   remaining suspect is a corrupted/garbage vtable pointer or trait-object
   field somewhere in the `g_pure_nvme_root_fat32.inner.device` chain at
   *runtime*, which the MIR-lowering-level `SIMPLE_DEBUG_METHOD_DISPATCH`
   identity check cannot see (it only proves the compile-time slot-index
   decision is correct, not that the runtime vtable data at that slot is
   valid). **Do not lift `vfs_boot_init.spl:374` permanently** — the skip
   must stay until this second defect is found. Handed off, not solved:
   next lane should disassemble further into `_device_sector_size` past the
   `self`-nil-guard shown above to find the actual indirect call/jmp that
   produces `0x0001e0ec8148e589`, and inspect the runtime layout of
   `SharedFat32Driver.inner.device` (the trait-object fat pointer / vtable
   pointer fields) at the point of construction vs. at the point of this
   call.
7. **`vfs_boot_init.spl:374` restored VERBATIM** to `if true:` before
   finishing this lane — confirmed via `sed -n '374p'` (`if true:`) and
   `git diff src/os/services/vfs/vfs_boot_init.spl` (0 lines).
8. **Evidence, gitignored, left for the next lane:**
   `build/os/_wkc8close/desktop.elf` (16.5 MB, the exact booted binary),
   `build/os/_wkc8close/native-build.out` (build log with the
   `SIMPLE_DEBUG_METHOD_DISPATCH` trace), `build/os/_wkc8close/
   serial.log.gz` (406 KB gzipped, 697700-line full boot transcript),
   `build/os/_wkc8close/qemu_stderr.log` (just the timeout-signal
   termination line, nothing else). The large regenerable `native-cache/`
   dir was removed after use. Files touched this lane, final state:
   `src/os/kernel/arch/x86_64/interrupt.spl` (new
   `spl_x86_on_kernel_ud2_fault` function, kept),
   `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` (ud2
   detection in `_rich_fault_entry`'s no-error-code recovery path, kept),
   `src/os/services/vfs/vfs_boot_init.spl` (touched then restored, `git
   diff` empty). No commits made this lane per the coordinator's hard rule.

### C8-DEEP lane (2026-07-17) — ROOT CAUSE FOUND & byte-level CONFIRMED:
### import-alias inconsistency — `use {SharedFat32Driver as Fat32Core}` then
### `Fat32Core.new(...)` binds the CONSTRUCTOR to the real `Fat32Core.new`
### while the type annotation + `.mount()` bind to the `SharedFat32Driver`
### alias, so a real Fat32Core box is dispatched as a SharedFat32Driver. NOT
### a trait-object / vtable / extra-deref / TypeId-collision defect — those
### were all downstream symptoms of one mis-bound constructor `call`.

**The whole C8 "trait-object extra-deref" framing is a red herring.** The
adapter trait-object box, its vtable, the dispatch codegen, and
`Fat32Core.new`'s field stores are ALL provably correct in the preserved
`build/os/_wkc8close/desktop.elf` (verified by disassembly + `objdump -s`
vtable dump — see items below). The storm is produced by exactly one
wrong compile-time method-resolution decision, which then walks a chain of
type-confused `self` pointers into a code-bytes-as-function-pointer call.

**1. The wrong call.** `src/os/services/vfs/vfs_boot_init.spl:379`,
`g_pure_nvme_root_fat32.mount("", "")`, where `g_pure_nvme_root_fat32` is
declared `Fat32Core` (line 96) and assigned `Fat32Core.new(g_adapter)`
(line 378). `Fat32Core` HAS its own `mount` method
(`Fat32Core.mount` @ `0x895c31f` in the ELF). But codegen emitted a call to
**`SharedFat32Driver.mount` @ `0x8dda17f`** instead (disasm at
`0x8e12d3c`: `movabs $0x8dda17f,%r9; call *%r9`, with `self`=the Fat32Core
box). Confirmed independently by the preserved
`SIMPLE_DEBUG_METHOD_DISPATCH` build log
(`build/os/_wkc8close/native-build.out:46`):
`[CODEGEN-METHOD-STATIC] in '_vfs_boot_init_pure_nvme_fat32'
func_name='SharedFat32Driver.mount' args=2`.

**2. Why that call storms (full byte chain, all addresses from the
preserved ELF).** `SharedFat32Driver` is `class { inner: Fat32Core; ... }`
and `SharedFat32Driver.mount` does `self.inner.mount()`, reading
`self.inner = [self+0]`. But `self` is really a **Fat32Core** box, whose
field 0 is `device: BlockDevice` (the NvmeBlockAdapter trait-object box).
So it calls `Fat32Core.mount(adapter_box)` →
`read_boot_sector(adapter_box)` → `_device_sector_size(adapter_box)`. Now
`self`=adapter_box (a `NvmeBlockAdapter`, which DOES carry a vtable header
at `[0]`). `_device_sector_size` does `device=[self+0]` = the vtable
address `0x8f42d78`; `vtable=[device]` = slot 0 = `NvmeBlockAdapter.read_sector`
@ `0x8e0e7d1`; `fn=[vtable+0x10]` = `[0x8e0e7e1]`. `read_sector` is only 14
bytes, so `0x8e0e7e1` lands inside the *next* method (`write_sector` @
`0x8e0e7df`) at its prologue+2: the 8 bytes there are
`89 e5 48 81 ec e0 01 00` = **`0x0001e0ec8148e589` = cr2, exactly** (LE of
`mov %rsp,%rbp; sub $0x1e0,%rsp`). `call *rax` to that non-canonical value
faults; the blind RIP+=2 recovery ISR walks unmapped space → the 69762-fault
storm. Every "prologue bytes as a pointer" observation across all prior C8
lanes was this one code-bytes read, not a trait-ABI defect.

**3. Root cause — an IMPORT-ALIAS resolution INCONSISTENCY (NOT a TypeId
collision; my first draft of this item was wrong and is corrected here).**
`src/os/services/vfs/vfs_boot_init.spl:20` is
`use os.services.fat32.shared_fat32_driver.{SharedFat32Driver as Fat32Core}`
— inside this file the name `Fat32Core` is an ALIAS for `SharedFat32Driver`
(while the *real* `Fat32Core` from `std.fs_driver` is also in scope
transitively). Line 96/378 read
`var g_pure_nvme_root_fat32: Fat32Core = Fat32Core.new(g_adapter)`. The
compiler resolves the SAME token `Fat32Core` two different ways:
- **type-annotation position** (`: Fat32Core`) and **instance dispatch**
  (`.mount()`) honor the alias → `SharedFat32Driver` /
  `SharedFat32Driver.mount` (proven: log line 46 `func_name=
  'SharedFat32Driver.mount'`, call @`0x8dda17f`; `.mount` is a real method
  of SharedFat32Driver so this half is self-consistent).
- **static-call callee position** (`Fat32Core.new`) IGNORES the alias and
  binds to the *real* `Fat32Core.new` @ `0x895861b` (proven: the call at
  `0x8e12ce0` targets `0x895861b` =
  `lib__nogc_async_mut__fs_driver__fat32_core__Fat32Core_dot_new`, and
  `SharedFat32Driver.new` is ABSENT from the ELF symbol table entirely — its
  only would-be caller was mis-bound, so `--gc-sections` stripped it).
Net effect: a *real* `Fat32Core` box (size `0xc0`, `device` at offset 0) is
constructed, stored into a slot the rest of the code treats as a
`SharedFat32Driver` (`inner: Fat32Core` at offset 0). `SharedFat32Driver.mount`
then reads `self.inner = [self+0]` = the Fat32Core's `device` field (the
adapter box) and calls `Fat32Core.mount` on it (`0x8dda334` → `0x895c31f`) →
the byte chain in item 2 → storm.

**4. Type-position honors the alias, call-callee position does not.** The
consistent half (`self.inner.mount()` inside SharedFat32Driver, `call
0x895c31f`) is the real `Fat32Core.mount` and is CORRECT — it only faults
because its `self` is the wrong object handed in by the mis-constructed
box, not because *its* resolution is wrong. The single defect is that
`AliasName.staticmethod(...)` does not apply the local `use ... as
AliasName` rename when a global type of the alias's *printed* name
(`Fat32Core`) also exists. Any file that aliases an imported type to a name
that shadows a real global type, then calls `Alias.staticfn(...)`, hits
this.

**5. Disproven hypotheses (do not re-chase):** trait-object fat-pointer
order; dispatch extra-deref in `compile_method_call_virtual`
(`closures_structs.rs:1406-1408` — correct for the boxed model);
`compile_struct_init` vtable-header vs field-0 collision (correct: adapter
box @ ctor `0x8e0aaf9` stores `&vtable` at `[0]`, fields at `[8]+`; vtable
slot 2 @ `0x8f42d88` = `0x8e0fc2c` = real `sector_size`); Fat32Core header
(it implements no trait, `device` at offset 0, stored correctly by
`Fat32Core.new` @ `0x8958ddc`). The duck-dispatch sentinel (C8-FIX) is a
genuinely separate, already-fixed bug; the `ud2`-recovery hardening
(C8-CLOSE) is correct and worth keeping. Both were real but neither is this.

**6. Fix (see below for landed state).** The correct behavior is that
`Fat32Core.new(...)` under `use {SharedFat32Driver as Fat32Core}` binds to
`SharedFat32Driver.new`, exactly as the type-position and `.mount()` already
do; then a real `SharedFat32Driver` is built and the whole chain is
type-consistent. Two ways to reach that:
- **(root, compiler)** make static-method-call callee resolution consult the
  file's import-alias map before falling back to the global type registry,
  so `Alias.staticfn` maps through the alias like type-position does.
- **(pragmatic, source)** drop the shadowing alias in `vfs_boot_init.spl`
  and refer to `SharedFat32Driver` directly (the alias only exists as a
  legacy rename and actively hides a same-named real type).
Skip at `vfs_boot_init.spl:374` remains `if true:` (verified `sed -n
'374p'`) — see item 7 for why it stays despite the C8 storm being fixed.

**7. FIX LANDED (root, compiler) + BOOT-VERIFIED.** Applied the root fix in
`src/compiler_rust/compiler/src/hir/lower/expr/simd.rs`
`lower_static_method_call`: resolve `class_name` through
`self.resolve_type_alias(...)` before building the qualified callee name,
mirroring `type_resolver.rs:116` exactly (non-aliased names are unchanged via
`unwrap_or`). Regression test added:
`hir::lower::import_loader::tests::aliased_import_static_method_call_resolves_to_alias_target`
(`use {Real as Alias}` + `Alias.make()` must emit `Global("RealWidget.make")`).
- **Hosted gate:** `cargo build -p simple-compiler` clean; new test passes;
  full `--lib` suite shows **zero stable new failures** (baseline 260 failing
  at HEAD; two runs with the fix gave 263/261 with a *non-overlapping* delta
  set of known env/timing/global-state flakes — watchdog timeout,
  configured-active-tier cache, runtime-bundle env — each passing in
  isolation).
- **Binary gate (fresh bootstrap seed, production recipe, skip lifted):**
  `SharedFat32Driver.new` (`0x08ddde74`) is now PRESENT and CALLED from all 3
  mount sites (was entirely ABSENT/gc-stripped before the fix); the
  `g_pure_nvme_root_fat32` constructor now targets it instead of the real
  `Fat32Core.new`. `nm | wc -l` = 7240 (healthy).
- **Boot gate (QEMU `-kernel`, NVMe attached, 130s):** the C8 storm is GONE —
  **zero** `0x0001e0ec8148e589`, serial log 952 lines (was 697700), ud2
  handler silent (0 `FATAL: kernel #UD`). With the skip LIFTED, `.mount()` now
  RUNS to completion through `read_boot_sector`/`_device_sector_size` and all
  scalar reads (clusters 2/5/7/3962), returning a graceful `Err`
  ("shared FAT32 root mount required/failed") — a functional result, not a
  fault. Framebuffer/engine2d/compositor come up and reach `pre-first-frame`.
  (NB: `-kernel` load, not OVMF pflash — matches C8-CLOSE's storm-repro
  methodology for an apples-to-apples codegen comparison; not a board-run
  claim.)
- **Scope honesty — "C8 storm removed" ≠ "VFS brought up".** The codegen
  blocker is gone, but `SharedFat32Driver.mount` still returns `Err` on this
  image; whether that is disk-content, lease geometry, or mount logic was NOT
  diagnosed this lane. VFS bring-up remains open work; only the fault storm is
  resolved.
- **First-frame: attempted, not confirmed-rendered.** Reached
  `compositor ready` + `[dbg-vbe] pre-first-frame` in BOTH configs, but
  **no** explicit `rendered`/`present`/`blit` marker appears in either serial
  log — the first render is *entered* and then faults in the draw_ir path
  (below), so "first-frame RENDERED" is not evidenced here (nor was it, given
  the render fault predates this lane; the C8 storm previously masked it).
- **Why the skip stays `if true:`, and the render faults.** A separate,
  non-C8 fault set in the `engine2d` GPU `draw_ir` path (`rip=0x88b112f`
  `engine2d_draw_ir_render_commands`, plus `0x8008860`/`0x80109cb` —
  scattered, bounded, ~650 recovered faults, NOT a storm) appears
  **identically with the skip ON and OFF** (second skip-on boot: same rips, C8
  storm still 0) — so it is independent of the **vfs mount path**. It is very
  unlikely fix-introduced (this fix alters codegen only for aliased *type*
  static calls; the active `baremetal-framebuffer` draw_ir path uses none —
  the sole engine2d alias is a *function* alias in the unused vulkan backend),
  but a true pre-fix A/B was NOT run (the pre-fix seed was overwritten), so
  this is stated as "independent of the mount path", not "predates the fix".
  Notably its `cr2=0x244c8d4c7500c640` LE-decodes to `40 c6 00 75 4c 8d 4c 24`
  (`movb`/`lea` opcode bytes) and increments (…640/648/650/651/652) — the SAME
  code-bytes-as-pointer *family* as C8, but in a DIFFERENT lowering (my
  static-call fix did not kill it, so likely an instance-method/vtable or
  another mis-resolved-call path). That is the next lane's lead. Skip restored
  to `if true:` and re-verified (`sed -n '374p'`).

**Follow-up (out of scope, flagged not fixed):** the pure-Simple compiler
(`src/compiler/35.semantics/resolve*.spl`, `10.frontend/.../cg_expr.spl`) has
its own static-method-call resolution; check it for the same alias gap so the
self-hosted binary is correct too when it builds the kernel (the current
kernel is seed-built, so the seed fix is what this boot verified).

**Files changed this lane:**
`src/compiler_rust/compiler/src/hir/lower/expr/simd.rs` (root fix),
`src/compiler_rust/compiler/src/hir/lower/import_loader.rs` (regression test).
`vfs_boot_init.spl` touched-then-restored (`git diff` empty).

**Evidence:** static addresses/bytes are from
`build/os/_wkc8close/desktop.elf` (disasm `scratchpad/desktop.disasm`);
fix-verification ELF/logs at `build/os/_wkc8deep/`
(`desktop.elf` skip-lifted, `desktop_skipon.elf`, `serial.log`,
`serial_skipon.log`); backups + baseline failure set at
`scratchpad/c8deep_backup/`.

## ALIAS-GAP lane (2026-07-17) — pure-Simple audit of the C8 alias-resolution bug class

Answers the "Follow-up (out of scope, flagged not fixed)" note above: does
`src/compiler/35.semantics/resolve*.spl` (and the HIR/MIR lowering that
actually performs static-call/constructor dispatch) have the same
alias-vs-consumer inconsistency that was root-caused and fixed in the Rust
seed at commit `3f0acf071cf`? **No — audited clean, and backed by a new
passing preventing test; no source fix was needed.**

**1. Why pure-Simple's architecture differs from the seed's.** The seed's bug
existed because `lower_static_method_call` (simd.rs) rebuilt the callee's
qualified name from the raw receiver token, independently of how
type-annotation resolution (`resolve_type_alias`) worked — two separate
resolution paths that could disagree. Pure-Simple resolves an import alias
**once, eagerly, at import registration** instead: `register_imported_symbol`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:400-419`) always
calls `self.symbols.rename_symbol(imported_type, imported_name)` for a
Class/Struct/Enum import, so the LOCAL alias symbol's canonical `.name` field
is unconditionally overwritten with the real target's own declared name.
Every downstream consumer that later reads that symbol's `.name` — directly
via `SymbolTable.get_symbol(id).name`, or via the `HirExprKind.NamedVar`
payload baked at Ident-lowering time
(`symbol_display_name`, `hir_lowering/expressions.spl:539`, itself documented
as returning "the CURRENT stored `.name`... reflecting any `rename_symbol`
call") — sees the SAME post-rename real name. There is structurally only one
source of truth, not one-per-consumer.

**2. Consumer paths audited (all converge on the renamed name):**
- **Type annotations**: `HirTypeKind.Named(symbol_id, _)` carries the same
  symbol id (`hir_lowering/expressions.spl` pattern lowering + `types.spl`).
- **Static method calls** (`Alias.method()`): HIR-level `MethodResolver`
  (`35.semantics/resolve_strategies.spl:288-343`, `is_static_method_call` /
  `resolve_static_method`) only matches a bare `Var(symbol)` receiver; a
  plain identifier like `Alias` always lowers to `NamedVar(symbol, name)`
  instead (see `hir_lowering/expressions.spl:489-540`), so this path is
  rarely hit for ordinary code and `resolution` stays `Unresolved`. The REAL
  dispatch decision is `50.mir/_MirLoweringExpr/method_calls_literals.spl`
  lines 2031-2046 (the `Unresolved` arm): for `NamedVar(sym, name)` it sets
  `static_receiver_name = name`; for `Var(sym)` it sets
  `static_receiver_name = static_def.name`. Both read the POST-RENAME name
  (see point 1), so they agree.
- **Constructor calls** (`Alias(args)`):
  `50.mir/_MirLoweringExpr/switch_operators_calls.spl:2224-2337`
  (`lower_call`)'s `direct_name` is likewise taken from the `NamedVar`
  payload's baked (post-rename) name before the `struct_field_order.has(direct_name)`
  construction dispatch.
- **Enum variant reclassification** (`Alias.Variant(...)` parsed as a
  MethodCall): `method_calls_literals.spl:827-845` reads
  `recv_enum_name` from the same `NamedVar` payload before consulting
  `enum_variant_index`.
- **Match patterns** (`case Alias.Variant(...)`) and struct-positional
  patterns: `hir_lowering/expressions.spl:895-941` resolves the pattern's
  bare enum/struct name via `self.symbols.lookup_or_invalid(...)` — the same
  scope lookup, returning the same renamed symbol id — traced by
  construction, not independently re-verified empirically (time-boxed out).
- **Trait-impl target names**: not independently traced this lane (same
  `HirTypeKind.Named(symbol_id, _)` mechanism applies architecturally; flag
  for a future pass if a trait-impl-specific alias bug is ever suspected).

**3. Empirical confirmation (new test, passing).** Wrote
`test/01_unit/compiler/hir/alias_static_call_resolution_spec.spl`,
reproducing the exact C8 collision shape: `use {RealWidget as Widget}` in a
consumer module while a genuinely different class **also literally named
`Widget`** is imported (under a different local alias, `DecoyWidget`) from a
separate module in the same compile unit — then asserts that both
`Widget.make()` (static call) and `Widget(value: ...)` (constructor) resolve
their `NamedVar` receiver/callee to `"RealWidget"` (both the baked display
name and the symbol table's own `.name`), never to the raw alias text or the
decoy. Verified via `bin/simple run test/01_unit/compiler/hir/
alias_static_call_resolution_spec.spl` — **2 examples, 0 failures**.
Sanity-checked the test can actually fail: temporarily changed the expected
value to a wrong marker, confirmed 2/2 failures with the real resolved name
(`RealWidget`) shown in the diff, then reverted — the assertions are live,
not vacuous.

**4. OS/services sweep for the same shadowing pattern (list only, not
refactored, per lane scope).** `grep -rn "^\s*use .*\bas\b" src/os/ src/app/`
(29 hits, excluding `test/` and one non-`.spl` `.rs.patch` file). Cross-checked
each alias's bare local name against real class/function declarations
elsewhere in the tree:
- **Confirmed, already-known collision (the C8 one itself):**
  `use os.services.fat32.shared_fat32_driver.{SharedFat32Driver as Fat32Core}`
  in `src/os/services/vfs/vfs_write_ops.spl:18`, `vfs_boot_init.spl:20`, and
  `vfs_init.spl:20`. A real, unrelated `class Fat32Core` genuinely exists in
  both `src/lib/nogc_sync_mut/fs_driver/fat32_core.spl:74` and
  `src/lib/nogc_async_mut/fs_driver/fat32_core.spl:71`. This is exactly the
  shape that caused the seed's fault storm (now fixed at the seed level,
  3f0acf071cf); per point 3 above, pure-Simple's own resolver already handles
  this shape correctly, so no action needed there — noting it here only
  because the lane's instructions asked for a sweep list, and it is the one
  live instance of the exact pattern.
- **Everything else swept uses a defensive, collision-avoiding rename** (the
  alias target is a unique, prefixed name, not a bare name that shadows
  something else) — e.g. `env_get as redis_env_get` / `as hook_env_get` / `as
  app_env_get`, `home as env_home` / `as app_home`, `cwd as app_cwd`,
  `ParseError as LibParseError`, `FileHandle as SharedFileHandle`, `DirEntry
  as SharedDirEntry`, `PayloadEntry as InitramfsPayloadEntry`,
  `progress_bar_html as shared_progress_bar_html`. No bare-name shadowing
  found among these.
- **One lower-confidence, different-shape note:** `use os.runtime.baremetal.
  runtime_minimal.{main as baremetal_main}` appears in all 5 arch `cstart.spl`
  files (`arm32`, `arm64`, `riscv32`, `riscv64`, `x86_64`, `x86_32`). Its bare
  alias text `baremetal_main` also happens to name a real, unrelated function
  `fn baremetal_main(args: [text])` in `src/app/cli/baremetal_cmd.spl:15`.
  This is a **function** alias, not a type alias — a structurally different
  consumer path from the one this lane's regression test covers, and
  `register_imported_symbol`'s function branch
  (`module_lowering.spl:446-449`, `qualify_imported_function_symbol`) only
  renames the symbol under `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` bootstrap
  mode (and even then to a qualified, not bare, name) — unlike the
  unconditional class/struct/enum `rename_symbol` in point 1. Practical
  exploitability looks low (the CLI subcommand module is unlikely to link
  into the same kernel/baremetal compile unit as `cstart.spl`), and this is
  outside this lane's scoped bug class (type/constructor alias resolution),
  so it is flagged here for awareness only — not reproduced, not fixed.

**5. Verdict / deliverable.** No pure-Simple source changes were made — the
audit came back clean, matching the "clean audit + passing preventing test is
success" criterion. New file:
`test/01_unit/compiler/hir/alias_static_call_resolution_spec.spl` (2 tests,
both passing). Backups of the probe script and the final spec are kept at
`scratchpad/aliasgap_backup/` for this session.

## MOUNT-ERR lane (2026-07-17) — mount() Err root-caused + fixed: silent phys=0 DMA bounce buffer

Follow-up to C8-DEEP's "mount returns graceful Err" handoff. Root cause was
(d)-family: `NvmeBlockAdapter` allocated its DMA bounce buffer via the raw
`SYS_ALLOC_DMA` syscall and **silently accepted a zero physical address**
under the freestanding boot. Every sector DMA then targeted phys 0 and read
back zeros, so `read_boot_sector` never saw `EB 58 90` / `0x55AA` and
`mount()` returned Err — no fault, no diagnostic.

**Fix** (`src/os/services/vfs/vfs_block_adapters.spl`, alloc path only):
route through `NvmeDriver.alloc_dma` so the existing phys==0 fallback
(`rt_dma_alloc`/`rt_dma_phys_of`) applies, and hard-fail with a descriptive
Err if either address is still zero (the zero-address guard is the
preventing measure — the silent-accept can't recur).

**Boot evidence** (QEMU NVMe, C8-fixed seed; serial saved at
`scratchpad/mounterr_backup/serial_mount_ok.log`): bounce `phys=0x157995008`
(was 0x0); boot sector probe read `b0=235 b1=88 b2=144` (=`EB 58 90`) and
`b510=85 b511=170` (=`0x55AA`); `shared FAT32 root mounted after direct
bootstrap`; `VFS ready (pure-Simple NVMe + FAT32)`; C8 storm count 0.
Probes were temporary (`# MOUNTERR-PROBE`) and are stripped from the landed
file; `vfs_boot_init.spl:374` remains `if true:` — lifting the skip for real
awaits a full green boot + render verification pass.

**Verification caveat:** the lane was killed by an API spend limit right
after the in-boot confirmation; the coordinator landed the clean backup
(diffed against origin: single hunk, alloc path only) and restored the
skip + stripped probes. A hosted unit test for this DMA path is not
practical (syscall + firmware behavior); the boot harness plus the
zero-address guard are the regression net.

**Also recorded (pre-existing, hit during re-verification):** the Rust seed
parser cannot parse an f-string used directly as a function argument in
`src/compiler/10.frontend/core/parser_preprocessor.spl`
(`expected Comma, found FString([Literal(")}"), Expr("value_tok")])`),
which currently blocks `<seed> test/run` on anything importing the
pure-Simple compiler tree. Known seed-grammar-gap family
(see bootstrap parser-fix chain); filed here so it isn't silently
worked around.

## PURE-SIMPLE ENTRY-CLOSURE grammar/ABI lane (2026-07-18) — current evidence, verification pending

The next Stage3 failures were source/ABI defects rather than evidence that a
managed Simple value was a usable C pointer. The pure parser's unary-expression
path does not accept prefix `&`, so forms such as `&buf as u64` fail before
codegen. Even where another compiler accepted the syntax, an array/text value
is a managed handle, not its payload address. Proven byte/word arrays now use
`rt_array_data_ptr_u8` / `rt_array_data_ptr`; text ABI slots use
`rt_string_data`. Wrappers whose current handlers ignore text payloads are
restricted to the exact kernel-equivalent value (empty log text or unveil
`"/"` + `"r"`) and otherwise fail closed. Syscall-written word
arrays are re-read through `rt_typed_words_u64_raw_data_at`. Direct handles and
`unsafe_addr_of` are not substitutes for array/text payload pointers.

The pointer-return migrations use explicit staging layouts already written by
the kernel: TaskInfo and its name use `[u64]` plus `[u8]` staging; DeviceInfo
uses two words, DeviceGrant uses fifteen words, and DMA results use two words.
Their userlib decoders consume raw staged storage rather than pretending a
tagged object is a packed userspace ABI struct.

Three free-function names also tokenized as reserved keywords and could not be
declared by the pure parser: `cli`, `bind`, and `spawn`. The live names are now
`disable_interrupts`, `socket_bind`, and `spawn_task`, with imports/callers
updated. This is a bounded source migration, not a parser change permitting
arbitrary keywords as free-function identifiers.

Kernel-handler audit found several wrappers whose previous success values were
not backed by payload behavior. They now fail closed at the userlib boundary:

- syscall 77's network forwarding path returns ENOSYS and defines no
  `NetIfInfo` output layout, so `ifconfig` passes no object pointer and reports
  the missing ABI;
- syscall 95 returns CPU count in `SyscallResult.value`, but Memory has no
  payload and Uptime is an explicit zero placeholder; syscall 96 returns only
  hostname length and syscall 97 does not copy/update the name. CPU uses the
  scalar result; the unsupported system APIs and aggregate `sysinfo` propagate
  errors;
- pledge implements only an empty capability list, unveil only the kernel's
  exact `"/"` + `"r"` behavior, and cap-grant has no canonical text encoding;
- log-write has separate level/facility slots but does not copy message bytes,
  and log-read returns only a count, not entries. Only an empty log message is
  representable; entry reads report unsupported;
- legacy VFS/mount wrappers do not match a completed kernel IPC/output
  contract and report unsupported instead of fabricating responses.

Focused regression coverage now includes
`test/01_unit/os/userlib/{device_syscall_result_buffer_spec,
process_syscall_result_buffer_spec,net_syscall_pointer_contract_spec,
system_syscall_result_buffer_spec,security_log_syscall_contract_spec,
syscall_pointer_marshalling_spec}.spl`, plus the Stage4 source-grammar contract.
The syscall-13 live fast path and its compact argv/priority ABI are covered by
the byte-identical mirrors
`test/{01_unit,unit}/os/kernel/ipc/spawn_binary_kernel_abi_spec.spl` and
`test/{01_unit,unit}/os/process_spawn_abi_spec.spl`. These mirrors currently
have scoped source checks and identity evidence only; executable Simple test
PASS remains pending.
On 2026-07-18 both
`scripts/check/check-simple-stage4-source-grammar.shs --self-test` and the live
source scan printed PASS. This is source-lint evidence only: the fresh full CLI,
focused specs, broader test suite, native kernel build, and boot/render evidence
remain pending while bootstrap continues. Do not promote this checkpoint to a
full verification PASS.

The first diagnostic full-CLI rebuild advanced past the userlib pointer/name
failures and stopped on eight multiline final-lambda arguments in
`test_executor_composite_jit_generic.spl`. Each call now has the trailing comma
required before the closing parenthesis, with a Stage4 smoke regression; the
stable-source rebuild is the next admission gate.

## Distinct generic registry and HIR array-pattern follow-up (2026-07-18)

The next full-closure parse stopped at the 1,000-entry `Result<T,E>` registry
limit even though many annotations repeated the same structural pair. Dict and
Result registration now intern an existing pair before testing capacity. The
focused registry spec covers 1,100 duplicate registrations, the exact 1,000th
distinct boundary, duplicate lookup after capacity, metadata reset, and stable
tag restart. High review found the change semantics-preserving.

A refreshed pure-Simple `bootstrap_main.spl` compiler built and passed the
candidate frontend admission gate. Its full-CLI build passed the former GHDL
parse tripwire, then crashed independently in HIR lowering. Kernel RIP and
`addr2line` placed the fault in the second `rt_for_iterable` inside
`HirLowering.lower_pattern`, the `PatternKind.Array` payload loop. The flat AST
bridge has no `PatternKind.Array` constructor, so this arm is unreachable on
the current frontend and is a seed-codegen false match. The arm was removed and
a source-contract regression was added.

The post-fix bootstrap compiler again built and passed candidate admission.
The bounded Vulkan reducer did not reach HIR before its 20-minute diagnostic
trace timeout, so it is inconclusive. The registry SSpec, HIR source contract,
full test-capable CLI, and full closure remain unverified; do not report this
lane or the wider font/SimpleOS goal as PASS and do not publish it yet.

Follow-up RIP evidence showed that deleting the unreachable Array arm only
moved the false match to the next shadowed arm, `PatternKind.Struct`. Struct
and Enum lowering now use the same runtime-discriminant predispatch pattern as
the established ExprKind Field/Block fix. The refreshed bootstrap compiler
built and passed admission, and the full closure advanced from 19 completed
HIR unit blocks to 956. It then exposed the same seed false-arm class in
`HirLowering.pattern_test_condition`: RIP `0x5fa8e4` is the iterable payload
read in its bare `case Struct(_, fields)` arm. This is the next bounded root
fix. The current checkpoint is still FAIL and must not be pushed.

## HIR false-dispatch follow-up (2026-07-18) — hard-cap stop

The PatternKind Struct/Enum family fix remains effective: three subsequent
full-CLI attempts completed HIR traversal without SIGSEGV or general-protection
fault. They then converged on the same ordinary diagnostic set instead of a
crash: 56,207 HIR errors, including 40,141 `unresolved type`, 15,321
`unresolved name`, and 728 untyped-return diagnostics.

Two high-reviewed sibling protections were admitted into refreshed
pure-Simple Stage3 compilers. Return scanning now discriminant-gates Stmt Expr
and Expr Return/Block/Field, and guards its Cast traversal/inference payloads.
The main expression lowerer also discriminant-gates its colliding Cast arm
while preserving real-Cast lowering with the former nil wrapper type.

Both refreshed compilers built and passed candidate frontend admission, but
each canonical full-CLI rebuild reproduced the exact same 40,141 unresolved
types. Binary hashes and changed-function disassembly proved the new source was
present; the first guarded run's only diagnostic delta was five extra
`return_scan_empty` references from the new guards. Therefore neither guard is
the root of the 40,141-error cascade. They remain preventive dispatch
contracts, not completion evidence.

The three-cycle session cap is exhausted. No candidate full CLI exists, font
specs/docgen remain blocked, and the branch must not be pushed. The next fresh
session must instrument the actual `lower_type` caller (or preserve a native
stack at `lower_named_kind`) before changing another dispatch arm; do not rerun
the same full build without new causal evidence.

## Fixed flat-type tag root cause (2026-07-19)

The next session instrumented the compiled-Stage3 full entry closure with
`SIMPLEOS_FOCUSED_HIR_DIAG=1`; retained evidence is in
`build/native_probe/hir-type-caller/full.log`. Bounded extraction with
`rg --pcre2 -o '\[(?:simpleos-flat-ret|flat-function-roundtrip)\][^\[]*'`
showed `_next_value` entering the bridge with raw fixed tag 4 (`text`) but
leaving as `i16`. `copy_cli_args_from` and `get_cli_args` entered with tag 5
(`[i64]`) but left as the unrelated arena identifier `print`. Corruption was
therefore inside flat-type conversion, before Module cache transport or HIR
symbol lookup.

Compiled Stage3 was misreading imported `TYPE_*` module values. The prior
literal workaround covered only tag 2; unmatched fixed tags could still enter
the expression-arena fallback, where slot 5 containing `Ident("print")` became
`TypeKind.Named("print")`. `parser_parse_type_impl` and
`parser_absorb_optional_suffix` now use the literal 0..33 wire protocol, so
`[text]` emits 6 instead of the observed 5. `convert_flat_type` decodes all
fixed tags literally, starts encoded dispatch at literal 500, and permits
expression access only for in-bounds tags in 34..499.

The canonical admission fixture now exercises `bool`, `text`, `[i64]`, and
`[text]` returns while preserving exact stdout `5`; it passed with the retained
pure-Simple Stage3 compiler. A focused compiled unit spec also checks raw tags
1/4/5/6/32 and their rich types.

The post-fix full closure completed HIR with zero `HIR lowering error`,
`unresolved type`, or `unresolved name` records and reached native link. This
removes the former 40,141-error cascade as the active blocker. The three
bounded link configurations then exposed runtime-bundle availability rather
than compiler semantics:

- `core-c-bootstrap` lacks hosted SDL2/Win32 runtime symbols;
- the compiler rejects removed `rust-hosted` and directs callers to
  `simple-core` or `core-c-bootstrap`;
- `simple-core` is not installed on this host and requests
  `SIMPLE_SIMPLE_CORE_PATH`/`SIMPLE_CORE_RUNTIME_PATH`.

Logs are retained under `build/native_probe/hir-fixed-cli/`. The mandatory
three-cycle cap is reached. No test-capable CLI was produced, so the focused
compiled unit spec, canonical font specs, docgen, full bootstrap, and live
render evidence remain pending. Do not publish this branch as verified until a
pure-Simple `simple-core` runtime archive is supplied and those gates pass.
