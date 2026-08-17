# Freestanding Entry Constants Become Zero Stubs

Status: OPEN (P1) — **kept open deliberately; NOT verified either way.** The row
has no reproduction recipe and its named artifact no longer exists in the tree.
See "Re-triage 2026-08-17".
Status re-verified 2026-08-17 by source inspection (triage shard 01).
  (Do not trust that stamp; it is not backed by anything reproducible.)

## Re-triage 2026-08-17 — unreproducible on this host, left OPEN

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
the stale Rust seed. No freestanding native build was run (~15 lanes share this
checkout; rebuilding/redeploying is prohibited).

Findings:

1. **The named subject file is gone.** `gui_entry_desktop.spl` does not exist
   anywhere under `src/` or `scripts/` (`find` + `grep -rl`, both empty), and
   `git ls-files 'src/os/**' | grep entry` lists no replacement carrying `FB_W`,
   `FB_H`, or `DIRECT_QEMU_TOTAL_MEMORY`. The only surviving near-match name is
   `src/os/kernel/arch/arm64/ramfb.spl:17` (`val ARM64_RAMFB_WIDTH: u32 = 1024`),
   an unrelated module-level `val`. Its last deletion appears in
   `6f86ff32a7db`, which CLAUDE.md records as the fourth tree-wipe commit, so
   the deletion may itself be wipe damage rather than an intentional removal —
   that is not resolved here.
2. **Half of the "Required Fix" is present.** `global_init_values` IS preserved
   through per-module mangling:
   `src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:263-292`
   ("Phase 2: Rename globals in mir.globals, global_init_values,
   local_globals") re-keys every `global_init_values` entry to the mangled name,
   with the parallel `global_init_strings` map handled the same way.
   `mir.local_globals` is likewise re-keyed (lines 336-341).
3. **The other half — entry-module `Node::Let` classified as data — IS present,
   in a file I first looked in the wrong place for.** My initial grep covered
   only `native_project/mod.rs` (where `Node::Let` genuinely does not appear;
   its `is_entry` uses at lines 959-968, 1340, 1374-1379, 1517-1526 concern
   `main`->`spl_main` renaming and object-cache eligibility). The classification
   lives one file over, and a parallel lane's "Source status 2026-08-17" section
   below is correct: `native_project/compiler.rs:350` has
   `let is_module_level_decl = matches!(item, Node::Let(_) | Node::Const(_) |
   Node::Static(_))`, with further `Node::Let` handling at lines 210, 273 and
   287, alongside `native_project/module_global_init.rs` and
   `native_project/entry_closure_global_init_tests.rs`. Recorded here as a
   correction so the wrong-place grep is not repeated a third time.

**Why this stays OPEN rather than being retired:** both halves of the "Required
Fix" now have source-side implementations (item 2 and the corrected item 3), but
the row's actual observable — weak text symbols with `xor eax,eax; ret` bodies in
a *Cranelift freestanding* symbol table — has never been re-observed after those
landed. No freestanding build was run in this triage or, per the parallel lane's
note, in the W4 wave. Retiring on "the required-fix code exists somewhere" plus
"the file that showed the symptom was deleted" would be classification by
absence, not by content, and a wrong close loses a real, silent, wrong-answer
defect in kernel hardware bring-up.

**What the next lane needs (this row currently has none):** an actual
reproduction — a two-file freestanding tree, entry file declaring
`val PROBE_W: u32 = 1024` read by an imported function, built with
`native-build --target x86_64-unknown-none --emit-archive`, then
`nm`/`readelf -sW` asserting `…__PROBE_W` is an `OBJECT` in a data section and
**not** an 8-byte `WEAK FUNC`. That is the missing control; without it neither a
fix nor a retirement can be proven.

Stage3 Cranelift freestanding builds emit module-level scalar `val`s declared
in the entry file as weak functions returning zero instead of initialized data.
Imported module constants are emitted as initialized data.

## Evidence

`gui_entry_desktop.spl` symbols such as `FB_W`, `FB_H`, and
`DIRECT_QEMU_TOTAL_MEMORY` appeared as weak text symbols whose bodies were
`xor eax,eax; ret`. Consequently PMM received zero bounds and BGA received a
zero requested mode, while PCI discovery itself remained valid.

## Required Fix

The native-project data-export/mangling pass must classify entry-module
`Node::Let` immutable globals as data and preserve `global_init_values` through
per-module compilation. Until fixed, early freestanding entry hardware values
are local immediates at their owning operations. They must not be replaced by
fake device readback or fixed evidence metadata.

---

## Source status 2026-08-17 (W4 bug-fixing wave)

The "Required Fix" above asks for two things. Both are present in source:

- **Preserve `global_init_values` through per-module compilation.**
  `src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:263-292`
  rewrites `mir.global_init_values` alongside `mir.globals` and `local_globals`
  under a "Phase 2: Rename globals in mir.globals, global_init_values,
  local_globals" header, re-inserting every entry under its mangled name and
  keeping unmangled ones. The map is no longer dropped across mangling.
- **Classify entry-module module-level declarations.**
  `native_project/compiler.rs:350` treats
  `Node::Let(_) | Node::Const(_) | Node::Static(_)` uniformly as
  `is_module_level_decl`, and `native_project/module_global_init.rs` exists
  specifically to carry module-global initialization. The sibling entry-file gap
  is separately pinned by
  `native_project/entry_closure_global_init_tests.rs`
  (`freestanding_entry_keeps_call_initialized_global_at_module_scope`).

**Not closed here.** The observable in this row is a *Cranelift freestanding*
symbol table (weak text symbols with `xor eax,eax; ret` bodies for `FB_W`,
`FB_H`, `DIRECT_QEMU_TOTAL_MEMORY`), which requires a stage-3 freestanding build
plus a QEMU boot to confirm — neither was runnable in this wave, and the
Cranelift adapter is outside this wave's file scope. Left **OPEN**, downgraded to
"awaiting a freestanding-build observation", with the source-side prerequisites
recorded above so the next lane does not re-derive them.

**Family:** the weak zero-returning body is the same fail-open mechanism as
`bytespan_starts_with_dropped_from_kernel_closure_weak_nil_stub_2026-07-28` and
`stage3_native_build_sigsegv_call_to_zero_root_cause_2026-08-11` — a symbol with
no real definition gets a fabricated zero body (or address 0) instead of failing
the build. See the FAMILY RESOLUTION section of the latter.
