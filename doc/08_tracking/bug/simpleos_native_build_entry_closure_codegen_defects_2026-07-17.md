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
