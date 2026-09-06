# Dangling-Reference Backlog — Root-Cause Grouping (2026-07-27)

Source: `sh scripts/check/check-dangling-references.shs` (checker landed in
`cfd676f39d9d`) over tracked `src/**/*.spl`, vendored trees excluded.

**Baseline total: 342 findings** — 54 MODULE, 274 SYMBOL, 14 METHOD.
(The "~350" figure in the original write-up came from a working copy with a few
extra local edits; 342 is the tracked-tree number.)

## Validation of the checker itself

Two whole-corpus cross-checks were run before grouping, and both say the
checker is **not** noisy:

* **MODULE findings: 0 false positives.** For all 31 distinct dangling module
  paths, the final dotted segment was matched against the basename index of
  every owned `.spl` file. Not one has a backing file anywhere in the tree
  under any spelling. The symlinked-tier concern (`frontend -> 10.frontend`,
  `std -> lib`) does not produce false positives here — the last-two-segment
  heuristic already absorbs it.
* **SYMBOL findings: 1 candidate false positive out of 196 distinct names.**
  All 196 flagged names were intersected against a declaration index built from
  every `fn|me|struct|enum|class|trait|mixin|actor|interface|impl|type|const|effect|union|val|var|let`
  declaration in owned `src/**/*.spl` (161,979 names). Only `Vec` intersects.
  The other 195 are declared nowhere and are true positives.

The 14-item manual audit finding "no false positives" is therefore corroborated
mechanically.

### False positives / checker-tightening notes

1. **`Vec` (SYMBOL, 1 site).** The only flagged name that has a declaration
   somewhere in the tree. Likely a builtin/prelude type whose real declaration
   is not in an owned `.spl` file, or a declaration form the pass-2 indexer does
   not register. Worth confirming before treating any `Vec` import as broken.

2. **FALSE NEGATIVE (more important than the above): basename self-match.**
   `src/lib/gc_async_mut/torch/dyn_ffi.spl:7` contained
   `use std.common.torch.dyn_ffi.*`. That module does **not** exist
   (`src/lib/common/torch/` holds `dyn_sffi.spl`, not `dyn_ffi.spl`), but the
   checker accepted it because the fallback rule "final segment alone matches a
   known module basename" was satisfied by *the importing file itself*
   (`dyn_ffi.spl`). Lines 8 and 9 of the same file were correctly flagged only
   because no file anywhere is named `dyn_ffi_ops` / `dyn_ffi_tensor_ops`.
   **Suggested tightening:** when applying the final-segment fallback, exclude
   the importing file's own basename from the key set. This is cheap and closes
   a class where a module and its stale sibling shim share a name.

## Group 1 — FIXED THIS ROUND: torch `ffi` -> `sffi` rename not propagated

* **Root cause:** the shared torch dynamic-FFI layer was renamed
  `dyn_ffi*` -> `dyn_sffi*`. Every tier shim was migrated
  (`src/lib/{common,nogc_sync_mut,nogc_async_mut,gc_async_mut,gc_sync_mut}/torch/dyn_sffi.spl`
  all exist and resolve), but one pre-rename leftover shim was never updated.
* **Count:** 2 MODULE findings (plus 1 checker false negative, see above).
* **Example:** `src/lib/gc_async_mut/torch/dyn_ffi.spl:8`
  `use std.common.torch.dyn_ffi_ops.*` — real module is
  `src/lib/common/torch/dyn_sffi_ops.spl`.
* **Why unambiguous:** the file's own header comment names its intended targets
  (`src/lib/common/torch/dyn_ffi_ops.spl`), and the real files are that exact
  path with the one-token rename applied. The sibling
  `src/lib/gc_async_mut/torch/dyn_sffi.spl` is the already-correct version of
  the identical shim, so the target spelling is confirmed by an in-tree twin.
* **Fix applied:** repointed all three `use` lines in
  `src/lib/gc_async_mut/torch/dyn_ffi.spl` at the `dyn_sffi*` modules and
  corrected the stale header comment. The file is retained rather than deleted
  because the parallel `src/lib/gc_sync_mut/torch/dyn_ffi.spl` documents itself
  as a deliberate "compatibility facade" for the legacy spelling; the alias now
  actually resolves.
* **Result:** 342 -> 340 for this change. Both target findings are confirmed
  gone from the re-run. The re-run's raw verdict reads 345 because the shared
  working copy is edited by parallel sessions: between the two runs, four new
  `use compiler.semantics.lint.primitive_types` MODULE findings (e.g.
  `src/compiler/35.semantics/lint/primitive_api.spl:18`) and one
  `source_file_coverage_identity` SYMBOL finding appeared from other agents'
  in-flight work. `diff` of the two run outputs shows exactly two removals —
  both mine — and five unrelated additions.

---

The groups below are **not** fixed. Each needs a decision that an import edit
cannot express.

## Group 2 — FUNCTIONAL GAP: BIP-39 wordlist module was never written

* **Root cause:** not a rename and not a deletion — the module never existed.
* **Count:** 1 MODULE + 2 SYMBOL.
* **Site:** `src/os/crypto/bip39.spl:19`
  `use os.crypto.bip39_wordlist.{bip39_word, bip39_word_index}`.
* **Evidence:** `git log --diff-filter=D -- 'src/os/crypto/bip39_wordlist.spl'`
  returns **no commits** — the path was never deleted, because it was never
  added. No file with `bip39_wordlist` in its name exists in the tracked tree,
  and no basename anywhere matches.
* **Impact — this is a real capability gap, not an import typo.** Both missing
  functions are on the live code path: `bip39_word(widx)` at
  `src/os/crypto/bip39.spl:159` (entropy -> mnemonic) and
  `bip39_word_index(word)` at `:189` (mnemonic -> entropy). Every public BIP-39
  entry point in the file is therefore non-functional. The rest of the module is
  complete and correct-looking (checksum handling, 11-bit regrouping), and its
  other dependency `pbkdf2_sha512_bytes` **does** exist at
  `src/lib/common/crypto/pbkdf2.spl:185` — the wordlist is the only thing
  missing.
* **What fixing involves:** authoring
  `src/os/crypto/bip39_wordlist.spl` with the canonical 2048-word BIP-39 English
  list plus `bip39_word(i) -> text` and `bip39_word_index(w) -> i64` (the latter
  wants a binary search or prefix map, since the list is sorted). Then validate
  against the Trezor `vectors.json` test vectors already cited in the file
  header. **Do not paper over this with an import edit** — there is no module to
  point at.

## Group 3 — module deleted / never landed, callers left behind

* **Root cause:** a module that whole subsystems import is absent from the tree.
  These are the same failure shape as the two incidents the checker was written
  for.
* **Count:** ~28 MODULE findings.
* **Largest member — `std.async_core`, 12 importers.** Every file under
  `src/lib/nogc_async_mut/async_host/` (`combinators`, `future`, `handle`,
  `joinset`, `promise`, `runtime`, `scheduler`, `unordered`, `worker_thread`)
  plus `async_host.spl:19`, `async_embedded.spl:23` and `async_unified.spl:23`
  import `std.async_core`. No file named `async_core` exists anywhere.
  Example: `src/lib/nogc_async_mut/async_host/future.spl:5`.
* **Other members:** `host.common.io.fs_ffi` (4, e.g.
  `src/compiler_rust/lib/std/src/host/common/io/fs_ops.spl:9`),
  `app.build.quality` (3, e.g. `src/app/check/render_adapter.spl:13`, importing
  `QualityResult`), the wine trio `common.wine_x86_64_decode` /
  `common.wine_vm_gate` / `common.wine_thread_adapter` (3, e.g.
  `src/lib/common/wine_cpu_exec.spl:5`), `simple_sdn` (2, e.g.
  `src/compiler_rust/lib/std/src/db/atomic.spl:6`),
  `std.common.math.field.fe_p256` (2, e.g. `src/os/crypto/p256.spl:21`),
  `std.math.bignum.bignat`, `std.crypto.md5`, `std.random_utils`,
  `std.common.unicode.codepoint`, `common.display_protocol.display_protocol`,
  `test.system.qemu.os.common.qemu_os_harness`,
  `compiler.core.compiler.mir_codegen`, and
  `compiler.hir.hir_lowering.module_registry` at
  `src/compiler/80.driver/driver.spl:45` — note this last one is the *same*
  module named in incident 2 of the checker's own header, so either the repair
  in `24ebf39ffcdc` did not cover this call site or it has since regressed.
* **What fixing involves:** per module, decide restore-vs-delete. Restoring
  means recovering the blob from history and re-landing it; deleting means
  removing the importers and whatever they feed, which for `std.async_core`
  means the entire `async_host` tier. Neither is a one-line edit, and
  `std.async_core` in particular should be triaged first because 12 files in the
  default async tier depend on it.

## Group 4 — dead example tree referencing a retired UI API

* **Root cause:** `src/compiler_rust/lib/std/examples/` still targets a UI
  surface (`ui.element`, `ui.attrs`, `ui.patchset`, `ui.gui.electron`,
  `ui.gui.vulkan_window`, `ui.tui.renderer_async`, `ui.widget_renderer`) that no
  longer exists under any spelling.
* **Count:** 9 MODULE findings across 4 files.
* **Example:** `src/compiler_rust/lib/std/examples/ui_cross_platform_complete.spl:14`
  `use ui.element`.
* **What fixing involves:** confirm the examples are unreferenced and delete
  them, or rewrite them against the current UI/DrawIR surface. Deletion is
  likely correct — these live under `compiler_rust/lib/std/examples/`, which is
  not on any build path — but it is a deletion decision, not an import edit, so
  it is out of scope for a low-risk round.

## Group 5 — case-collision: mega-prefix SI unit modules never created

* **Root cause:** the SI mega- prefix modules collide case-insensitively with
  their milli- siblings (`Mm.spl` vs `mm.spl`, `Mg.spl` vs `mg.spl`,
  `MW.spl` vs `mW.spl`). Only the lowercase member of each pair exists, so the
  mega- units are simply absent — a real gap, not a spelling error, and one that
  will recur on any case-insensitive filesystem.
* **Count:** 3 MODULE + 3 SYMBOL.
* **Example:** `src/unit/simple-lang/length/__init__.spl:23`
  `use unit.length.Mm.{Megametre}` — `src/unit/simple-lang/length/` contains
  `mm.spl` (millimetre) and `Gm.spl` (gigametre) but no `Mm.spl`.
* **Affected units:** `Megametre`, `Megagram`, `MegaWatt`.
* **What fixing involves:** create the three modules under names that cannot
  collide case-insensitively (e.g. `megametre.spl` / `megagram.spl` /
  `megawatt.spl`) and update the three `__init__.spl` imports to match. Cheap,
  but it changes the public module-path convention for the unit tree, so it
  needs a naming decision first.

## Group 6 — symbol renamed or never exported (largest group)

* **Root cause:** the module resolves, but a name in its `.{...}` list is
  declared nowhere in the tree. Mostly renames whose importers were not updated,
  plus a few names that were only ever planned.
* **Count:** ~265 SYMBOL findings — the bulk of the backlog. 195 of the 196
  distinct flagged names are confirmed undeclared anywhere (see validation
  above).
* **Densest sites:** `common.window_protocol.window_protocol` (6 names),
  `std.fs_driver.nvfs_hosted_driver` (5),
  `os.services.netstack.tcp_state_machine` (4), `host.common.io.types` (4),
  `super.list_utils` (3), `std.report.emitter.lsp` (3),
  `os.compositor.display_backend` (3), `host.common.net.types` (3).
* **Example:** `src/app/cli/query_commands.spl:22` imports `LspEmitter` and
  `LspCodeAction` from `std.report.emitter.lsp`; neither name is declared in any
  owned `.spl` file. `LspEmitter` is imported from three separate call sites
  (`query_check.spl:16`, `query_commands.spl:22`, `query_navigation.spl:12`),
  so this one symbol alone accounts for three findings.
* **What fixing involves:** per symbol, find the current name in the target
  module and rewrite the import, or implement the missing declaration. This must
  be done symbol-by-symbol with the target module open — there is no safe bulk
  transformation, which is why it is deliberately left for later rounds. Working
  by densest module (window_protocol first) clears the most findings per unit of
  review.

## Group 7 — methods called but defined nowhere

* **Root cause:** `self.foo(...)` where neither `me foo` nor `fn foo` exists
  anywhere in the tree — incident 1's exact shape. The checker only flags a
  tree-wide definition count of zero, so each of these is a genuine
  call-into-the-void on whatever path reaches it.
* **Count:** 14 METHOD findings.
* **What fixing involves:** per call site, implement the method or delete the
  call. Small enough to clear in a single focused round, and the highest
  severity-per-finding of any group here, since each one is a runtime failure
  rather than a compile-time import error.

## Suggested order for later rounds

1. **Group 7** (14) — smallest, highest severity per finding.
2. **Group 3 `std.async_core`** (12) — one decision unblocks the whole
   `async_host` tier; also re-check the `module_registry` regression at
   `driver.spl:45`.
3. **Group 4** (9) — likely a straight deletion once the examples tree is
   confirmed dead.
4. **Group 2** (3) — write the BIP-39 wordlist; self-contained and testable
   against published vectors.
5. **Group 5** (6) — needs a naming decision, then trivial.
6. **Group 6** (~265) — grind by densest module.

Alongside, apply the checker tightening in the false-negative note so stale
sibling shims stop hiding behind their own basename.
