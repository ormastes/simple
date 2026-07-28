# Stage-4 Campaign Summary and Handoff — 2026-07-27

Consolidation of ~15 reports and bug docs plus a dozen commits produced during
the 2026-07-27 Linux x86_64 stage-4 campaign. Written so the next session does
not have to reconstruct the story from primary sources.

**Scope note:** several source reports were written into the repo and then lost
to a later sync. Six of the sixteen inputs below are recoverable only from git
history, not from the working tree. Recovery shas are given in the
[Source index](#source-index).

---

## 1. Bottom line

**Stage 4 still FAILS. No deploy occurred.**

- `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` is still the
  2026-07-25 **Rust seed** (size `145290352`, matching the size recorded in
  `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` §7; the file's
  mtime has since been touched to 2026-07-27 22:06, but the size is unchanged
  and no self-hosted binary was installed).
- The four RISC-V gates therefore keep their **seed baseline**, re-confirmed at
  `simple_riscv_hardening_2026-07-27.md:542-543` and `:445-457`:

  | Gate | Result |
  |---|---|
  | `check-riscv-rtl-truth.shs` | **PASS** (exit 0, `riscv_rtl_truth_ok=true`, `unknown=0`) |
  | `check-riscv-hardware-gates.shs` | **13/22 PASS** (exit 1; expected 21/22) |
  | `check-riscv-formal-dual-track.shs` | **FAIL** (exit 1) |
  | `check-riscv-product-level-evidence.shs` | **FAIL** (exit 1) |

**This is an unfinished milestone, not a regression.** Per the history
archaeology (`stage4_history_timeline_2026-07-27.md`), **Linux x86_64 has never
had a green stage-4 deploy** in this repo's history. Every Linux-side stage-4
doc from 2026-07-08 through today ends in "blocked" or "deploy did not occur" —
never "was green, then broke." The single documented green full-CLI deploy on
record is **macOS aarch64 only**: commit `5dbe1bc31f3` (2026-07-25 03:29),
`doc/03_plan/compiler/bootstrap/stage4_macos_deploy_2026-07-25.md`, gate 11/11
PASS. Different platform, different binary, different build lane. No retraction
of that macOS claim was found.

There is no Linux green baseline to have regressed from.

---

## 2. Trajectory

All within one day, one tree, strictly *after* the deterministic segfault at HIR
module 32 was removed:

```
47,513 -> 11,826 -> 5,950 -> 4,008 -> 2,224 -> 1,681 -> 1,077
```

| Step | Cause of the drop | Commit |
|---|---|---|
| 47,513 -> 11,826 | round-4 opaque-symbol-registration guard | (pre-`9b612a11418c` guard rounds, later reverted) |
| 11,826 -> 5,950 | facade **export-list** sweep for star imports (`MirType` 760 -> 37) | `67024e9c0a51` (a) |
| 5,950 -> 4,008 | *(same commit, second mechanism)* | `67024e9c0a51` |
| 4,008 -> 2,224 | one-level **transitive star-import** surfacing (`mir_operand_copy` 393 cleared, `cranelift_*` cleared) | `67024e9c0a51` (b) |
| 2,224 -> 1,681 | `me` / `self` receiver alias | `8af2dc555960` |
| 1,681 -> 1,077 | symlink module-spelling normalization (clears the whole `lex_*` family to zero) | `3eea09c67960` |

Throughout: **zero segfaults**, and **all ~1,752 HIR modules lowering**. This is
the signature of newly-unblocked progress, not oscillation around a prior
working state.

### The count is inflated ~28% by duplicate reporting

`src/compiler/{frontend,backend,blocks,mir_opt,...}` are symlinks to the
numbered layer dirs (`10.frontend`, `70.backend`, ...), and `src/std` is a
symlink to `lib`. **The same physical `.spl` file is lowered and reported under
two or three different qualified module aliases.** Confirmed pairs:

- `compiler.core.lexer_scanners` (304) == `compiler.10.frontend.core.lexer_scanners` (304) — one file, `src/compiler/10.frontend/core/lexer_scanners.spl`
- `ptx_builder` 23/23; `cranelift_codegen_adapter` 6/6/6
- `std.*`/`lib.*` variants: `database.sql.statement` 19/19, `gpu.engine2d.backend_session` 16/16/16, `db_atomic` 14/14

Summing confirmed excess over the top-modules list alone gives **~468 of 1,681
lines (~28%) that are literal duplicate reports** of an error already counted
under another alias for the identical file and line. That is a **lower bound**
— smaller pairs in the 157-module tail were not individually verified.

**Do not treat the raw count as a distinct-site count.** The distinct-site
number is materially lower.

---

## 3. Root causes found

### 3.1 The two native `Dict` defects — the real unblock

`doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
(severity high, **OPEN**) and
`doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`
(severity high, **OPEN**).

- **`Dict.get(k)` is unsafe on a HIT.** `V=i64` returns a still-boxed value
  (`7` came back as `56`, i.e. `7<<3`); `V=struct` returns a non-nil Option
  whose `.unwrap().name` **segfaults**. Misses are correct (nil); `keys()`,
  `contains_key()`, `d[k]` and `Some(d[k])` are all correct.
  Mechanism: `.get()` lowering
  (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1244-1262`)
  uses single-layer value-type resolution (`local_mir_type_of`) and lacks the
  index-read path's post-decode `struct_value_syms[decoded.id]` registration
  ("Bug #189" block, `expr_dispatch.spl:1005-1029`), so `resolve_field_index`
  cannot recover struct identity.
- **`Dict.len()` returns `-1` for every dict**, populated or empty, local or
  struct-field, while `.keys()` correctly reports the real count. Erased-receiver
  `.len()` falls through to `rt_len` -> `rt_string_len`, which returns `-1` for
  non-string handles (`src/runtime/runtime_native.c:1741-1745`).
  The `functions.len() < 0` "partial module" heuristic built on this signal
  fired **35,483 times in a single stage-4 run**.
  Explicit warning in the bug doc: **do not "fix" `rt_string_len`'s `-1`.**

Evidence that proved it: direct probes showing `56` for a stored `7`, and
`.keys()==2` while `.len()==-1` on the same dict.

**Fix (caller-side workaround only): `9b612a11418c`** — rewrite `module_lowering.spl`
lookups to `contains_key` + index read, and revert six commits of guard rounds.
The codegen defects themselves are **still open**; only the callers were moved
off the broken primitives.

This was the true root cause of the stage-4 segfault at HIR module 32, and
removing it is what made the whole error-count campaign possible.

**Update 2026-07-28: the `.get()` codegen defect itself is now fixed**, not
just worked around — see [§8.2](#82-the-dictget-root-fix-landed-not-just-worked-around).

### 3.2 The `me` prefix-form receiver

`doc/08_tracking/bug/stage4_me_receiver_unresolved_in_class_methods_2026-07-27.md`
— **FIXED** by `8af2dc555960`.

`unresolved name: me` appeared **543 times**, all under `src/app/office/*`
(sheets 80, word 55, planner 44, mail 43). The prefix form `me foo():`
synthesizes a receiver named **`"self"`** (`parser_decls_use.spl` ~line 457),
and `me` is never handled in `parser_expr.spl` — so it survives as
`Ident("me")`. Fix: alias `me` <-> `self` in `lower_unresolved_ident`
(`src/compiler/20.hir/hir_lowering/expressions.spl:219-231`).

Result: **543 -> 0** (see §4b — the widely-quoted "543 -> 20" is wrong).

### 3.3 Symlink module spellings break directory-package siblings

`doc/08_tracking/bug/module_spelling_symlink_breaks_package_siblings_2026-07-27.md`
(severity high, **PARTIALLY FIXED** by `3eea09c67960`; recover from
`ef2b8db2185`). Audit: `symlink_module_spelling_sibling_audit_2026-07-27.md`.

`_driver_module_name_from_path`
(`src/compiler/80.driver/driver_source_loading.spl:55-100`) derives the dotted
module name **purely lexically** and never calls `realpath`, and
`_driver_canonical_source_path` (`:102-122`) is documented as deliberately
lexical-only. So two paths to one physical file yield two different module
names, and `_driver_unique_physical_sources` keeps the first spelling **per
file**. `lexer.spl` registered only as `compiler.frontend.core.lexer` while its
sibling `lexer_scanners.spl` registered under two *other* spellings.
`resolve_package_sibling_symbols`
(`module_lowering.spl:881-916`) implements directory-package semantics by raw
**dotted string prefix match** with no normalization — so two files in one
physical directory with different prefixes are simply not siblings, and every
bare cross-file call between them fails.

That produced **~530 errors** from that one package. Fix `3eea09c67960`
(15 insertions, `driver_source_loading.spl`) mirrors
`compiler.10.frontend.core.*` -> `compiler.core.*`: **1,681 -> 1,077** (604
fewer), `lex_*` family to zero (`lex_make_token` 160, `lex_advance` 116,
`lex_peek` 70, `lex_pos_get` 60 — matching call-site counts in
`lexer_scanners.spl` of 80x/58x/35x/30x).

**It is a one-package patch.** `compiler.frontend.treesitter.*` is still broken,
carrying the **185 `TokenKind`** errors. See §6.2.

Bulk builds are safe — `_driver_collect_sources` uses `find` without `-L`, so
the whole-tree walk never traverses a symlink. The hazard is specific to the
entry-closure / native-build path (`SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE`).

### 3.4 Facade `export` lists not consulted by glob imports

`doc/08_tracking/bug/stage4_focused_subbuild_star_import_unresolved_2026-07-27.md`
(severity high, `fixed_by: 67024e9c0a51`, partial).

The original **closure hypothesis was DISPROVEN** — only 127 import-misses total,
and `mir_data` was found (`found=true`). The real causes were both in glob symbol
*registration*:

1. facade export lists were not swept for star imports (`items.len()==0` skipped
   the loop) -> **5,950 -> 4,008**, `MirType` 760 -> 37;
2. one-level transitive star imports were not surfaced -> **4,008 -> 2,224**,
   clearing `mir_operand_copy` (393) and the `cranelift_*` family.

Baseline histogram at 11,826: MirType 760, me 543, mir_operand_copy 393,
MirTypeKind 317, MirConstValue 197, TokenKind 185, lex_make_token 160,
MirOperand 158.

Mechanism (a) — sweeping an author-declared `export` list — is uncontroversial
and should be kept. Mechanism (b) is contested; see §6.4.

### 3.5 `export NAME from MODULE` unsupported by the parser

`doc/08_tracking/bug/flat_ast_export_from_and_type_alias_loss_2026-07-27.md`.

`export X from module` kept only `X` and **dropped the provider module entirely**
from `Module.exports`, so `find_reexport_source` could never chase it. Cause:
`from` is a plain `TOK_IDENT` — there is no `TOK_KW_FROM`. (The same doc records
two adjacent losses: flat parsing does not dispatch `type Name = Target`, and
module assembly hardcodes `type_aliases: {}`.)

Scale: **223 such lines across 14 files** were silently dropping their source
module, accounting for **~110 unresolved-name errors** in the
`FixConfidence`/`Replacement`/`EasyFix` family alone.

**Fixed by `e0f6d761320`** (`parser_decls_use.spl`, 43 insertions, 0 deletions).
Bare module names are emitted as relative (`"." + name`).

Corroborating detail from the classification report: the `easy_fix/__init__.spl`
facade already carried the author's own comment — *"`export X from module` loses
`module` in the current bridge, so use explicit import-form re-exports"* — i.e.
the authors had hit this bug and worked around it without filing it.

### 3.6 Genuinely missing imports

Not a compiler bug — real source defects, most likely masked historically by the
interpreter's flat global-symbol registry (a documented landmine: interpreted
execution resolves bare names via a flat registry that native HIR lowering does
not use), so these call sites never needed an explicit import until strict
native lowering.

Confirmed instances:
- `PrimitiveType` (36) — `src/compiler/70.backend/backend/cuda/ptx_builder.spl`
  uses it at lines 148, 160, 210-218 but its import block (lines 6-10) has **zero
  import path** to `compiler.backend.common.type_mapper` where it is declared
  (`type_mapper.spl:221`). `cuda_type_mapper.spl` glob-imports it, but that glob
  is local to `cuda_type_mapper` and is not transitively visible.
- `error` (28) / `panic` (26) — e.g. `type_mapper.spl:98` calls bare
  `error("...")` with no `error`/`panic` import of any kind in lines 6-8.
- `metal_sffi_*` (20, the real content of the phantom "residual me" — see §4b):
  three functions defined in `src/lib/nogc_sync_mut/io/metal_sffi.spl:68,80,91`
  reach `gc_async_mut` through a two-hop facade chain whose **middle hop**
  (`src/lib/nogc_async_mut/io/metal_sffi.spl:9`) is an explicit enumerated
  `export use` list that ends at `metal_create_swapchain` and predates the
  quarantine/reap additions. The wildcard at hop 1 can only re-export what hop 2
  exported. **Source fix**, landed as `3721346d70a`.

### 3.7 `text(x)` is not valid Simple

`doc/09_report/stage4_residual_me_and_text_2026-07-27.md`, CLASS 2 —
**COMPILER bug, still open.**

`unresolved name: text` = **48**, and it is *stable*: 48 in both repro24 (1,681
total) and repro25 (1,077 total). It did not move at all while the total fell by
604 — it is fully independent of the import-resolution work.

All 48 are **16 distinct sites x 3 module aliases** in one physical file,
`src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl` (lines 218, 258, 295,
321), all of the call form `text(<expr>)` used as a stringify.

Mechanism, proven from compiler source: for a `Call` whose callee is a bare
`Ident` with one unnamed argument, lowering consults `primitive_cast_type_kind`
(`expressions.spl:285-303`) and emits a `Cast` on a hit. The table
(`expressions.spl:60-79`) covers **only** fixed-width numerics — no `text`/`str`
arm. `text` is also absent from `is_interp_builtin_fn` (`expressions.spl:51-58`,
which carries `to_string`, `str`, `int`), and no `fn text(...)` exists anywhere
in `src/`. So it falls through to `lower_unresolved_ident`.

The asymmetry that makes this a compiler bug rather than a source bug: `text`
**is** accepted as a type name at `types.spl:463`
(`case "text" | "str" | "String": HirTypeKind.Str`). The type checker knows
`text`; the cast table does not.

Latent blast radius: **10 further files** use the same form and will hit this the
moment they are lowered (`game2d/render/{draw_batcher,texture_atlas,canvas}.spl`,
three `play/locator.spl` tiers, `browser_engine/{dom,script/canvas_api}.spl`,
`common/ui/builder.spl`, `common/render_scene/scene.spl`).

Suggested fix: add `text` to `is_interp_builtin_fn` alongside the existing `str`
precedent (smaller change), or extend `primitive_cast_type_kind` and confirm the
MIR side stringifies. The `.to_text()` workaround should **not** be the fix.

---

## 4. Corrections to the record

These are the parts of today's story most likely to be re-derived wrongly.
Stated bluntly.

### 4a. Two root-cause theories were falsified, and five guard rounds were built on a false signal

- **The "header-only / partial module" theory is dead.**
  `doc/08_tracking/bug/hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`
  is **SUPERSEDED** by the two Dict bug docs. Its "nil decl dicts" framing was
  an artifact of `Dict.len()` returning `-1` — an in-place `Module` with
  `functions: {}` already reads `fns=-1`, so nothing was ever "header-only".
- **The "struct-field map copy" theory is INVALID.**
  `doc/08_tracking/bug/native_struct_field_map_copy_nilfills_nested_dicts_2026-07-27.md`
  — premise not reproducible, no copy involved, no minimal repro ever built;
  `idx_fns=-1` was again the `.len()` artifact. (Its severity field still reads
  High and should be corrected.)
- **Five guard rounds plus a module-global registry were built on the false
  `Dict.len() == -1` signal, then fully reverted.** The registry workaround
  (`9f8d5a7a1945` + `797497d757bd`) and the guard commits (`ea697e4c2a85`,
  `8fb1d047f9f3`, `c62b2c72c659`, `dd64ffbddb69`, ...) were all reverted by
  `9b612a11418c`. Reverting them was correct — they rested on an unsound
  predicate.

The lesson worth carrying: a heuristic that fired **35,483 times in one run**
was measuring a runtime bug, not a program property.

### 4b. The "residual 20 `me` errors" figure was a grep artifact

| Pattern | repro24 | repro25 |
|---|---|---|
| `grep -c "unresolved name: me"` (substring) | 20 | 20 |
| `grep -cE "unresolved name: me$"` (anchored) | **0** | **0** |

There are **zero** occurrences of `unresolved name: me` in either log. All 20
substring hits are `unresolved name: metal_sffi_*` — the substring `me` matching
the prefix of `metal_`
(`metal_sffi_release_uncommitted_submission` 12, `..._reap_submission_quarantine` 6,
`..._quarantine_submission` 2).

**The real result of `8af2dc555960` was 543 -> 0, not 543 -> 20.** The `me` class
is closed. Corrected in the bug doc by `86f02c8352c` (29 insertions, 6 deletions);
`aa8e7e684e9` is an empty subject-only commit announcing the same.

The 20 `metal_sffi_*` errors were a real but unrelated source defect (§3.6),
fixed by `3721346d70a`.

**Always anchor the pattern when counting a symbol class.**

### 4c. The "1,219 modules, zero unresolved" claim was premature

That run was killed before reaching the phase where unresolved-name errors are
emitted. A module count with no error count is not evidence of a clean build.
Do not cite it.

---

## 5. Breakages found on main

Two undefined-symbol references reached `main` via a sync commit that
resurrected reverted code. Both were **inert by construction** at the time,
because the gates gating them read `Dict.len()` — which returns `-1`, so the
branches either never ran or always ran into the dead path.

### 5.1 `register_glob_imported_symbols_depth` / undefined `depth`

`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:761,765`:

```
if depth == 0 and declaration_count == 0 and glob_imp.items.len() == 0:
    ...
    self.register_glob_imported_symbols_depth(nested_mod, nested_key, import_span, depth + 1)
```

`register_glob_imported_symbols` is declared at `:693` as
`me register_glob_imported_symbols(imported_mod: any, imported_mod_name: text, import_span: Span)`
— **no `depth` parameter**. `depth` is not a field of `HirLowering`
(`hir_lowering/types.spl:44` declares `loop_depth`, not `depth`) and not a
module-level binding. `register_glob_imported_symbols_depth` is **defined nowhere
in the repo** — a repo-wide grep returns exactly one hit, the call site itself.

Provenance: `69b1b2ab5dc "sync gh and push"`, whose parent is `834006c5afa`,
**not** `67024e9c0a51`. That sync *replaced* the 40-line inline transitive sweep
`67024e9c0a51` had added with a guarded call to a helper that does not exist —
a textbook instance of `.claude/rules/vcs.md` § "Sync must never clobber."

Consequence: any measurement of "(b) reduces errors 4,008 -> 2,224" describes
`67024e9c0a51`'s tree, **not HEAD**.

### 5.2 `hir_registry_*` after `module_registry.spl` was deleted

`9b612a11418c` deleted `src/compiler/20.hir/hir_lowering/module_registry.spl`
(51 lines; the file is confirmed absent) but left three live references:

- `src/compiler/80.driver/driver.spl:45` —
  `use compiler.hir.hir_lowering.module_registry.{hir_registry_reset, hir_registry_put}`
- `module_lowering.spl:462` — `if hir_registry_contains(part_hop.module_name):`
- `module_lowering.spl:463` — `part_src = Some(hir_registry_get(part_hop.module_name))`

`grep -rn "hir_registry" src/ --include=*.spl` returns **only these three lines**;
there is no definition of any of the four names anywhere in the tree. The revert
kept the *consumer* of the header-only fallback while deleting its *provider* —
a half-state strictly worse than either finishing the removal or restoring the
registry.

### 5.3 Status: STILL LIVE at HEAD — verified, not repaired

**Correction to the working assumption.** Both breakages were re-verified at
HEAD `3721346d70a` while writing this summary and **both are still present**:

```
$ grep -rn "hir_registry" src/ --include=*.spl
src/compiler/80.driver/driver.spl:45:use compiler.hir.hir_lowering.module_registry.{hir_registry_reset, hir_registry_put}
src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:462: if hir_registry_contains(part_hop.module_name):
src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:463:     part_src = Some(hir_registry_get(part_hop.module_name))

$ grep -rn "register_glob_imported_symbols_depth" src/ --include=*.spl
src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:765: self.register_glob_imported_symbols_depth(...)

$ ls src/compiler/20.hir/hir_lowering/module_registry.spl
ls: cannot access ...: No such file or directory
```

`70a75df5a18` and `b0698c98307` touched `module_lowering.spl` after the fact but
did **not** remove these. **Repairing them is the first task for the next
session.** Smallest correct repair: delete `driver.spl:45`, rewrite
`module_lowering.spl:461-463` to `contains_key` + index against
`self.modules_by_name`, and delete the `:757-765` nested-sweep branch (keeping
the `glob_imp.items` loop at `:766-771`).

### 5.4 Related, still open: three struct-valued `.get()` survivors

`9b612a11418c`'s message claims "all 14 struct-valued dict lookups converted."
That is **false**. `Module` is a struct (`parser_types.spl:19`), so
`Dict<text, Module>.get()` is exactly the corrupt-Option case. Survivors:

- `module_lowering.spl:461` — payload field-read at `:465`, passed as `Module` at `:466`
- `module_lowering.spl:763` — payload passed to the undefined depth helper
- `module_surface.spl:260` — same defect class, outside the audited file

### 5.5 Why a seed build did not catch any of this

Every one of these commits reports "Seed-build N verified." A seed build cannot
surface findings 5.1 or 5.2: in the seed lane `Dict.len()` is **correct**, so the
`functions.len() < 0` gate at `:457` is false, the branch containing the
undefined names is never evaluated, and the unresolved `use` at `driver.spl:45`
fails soft (both imported symbols are unused after the revert).

**A seed build is not a sufficient gate for changes to native-only code paths.**
The minimum extra gate is static and cheap: assert every called name in
`module_lowering.spl` has a definition. That grep would have caught both.

---

## 6. Open items, ranked

Ranked by evidence, not by size of the raw count.

### 6.1 Duplicate-alias reporting (~28% of the count) — LOW effort, highest leverage

~468 of 1,681 lines (lower bound) are duplicate reports of the same physical
file under symlink-derived aliases. One fix in the focused-native-build driver's
module-dedup/visited-set logic — or collapsing symlink-derived aliases before
reporting — removes it. Until this lands, **every error count in this campaign
is inflated by an unknown but substantial factor**, which distorts the ranking
of everything below it.

### 6.2 The general canonicalization fix — per-package patches do not scale

`3eea09c67960` fixed exactly one subpackage. The audit
(`symlink_module_spelling_sibling_audit_2026-07-27.md`) quantifies why that
approach is a dead end:

- **17 unnumbered->numbered symlinks** under `src/compiler/`; only
  `compiler.10.frontend.core.*` has an alias branch. Every other tier
  (`backend`->`70.backend`, `blocks`->`15.blocks`, `mono`->`40.mono`, ...) has
  the identical defect, unfixed.
- **`src/std -> lib` alone has 38 DISJOINT physical directories** — directories
  where two files share *no* dotted package prefix and therefore can never be
  siblings. Of 3,647 resolved `std.*`/`lib.*` imports, 2,857 land under
  `src/std/...` and 790 under `src/lib/...`.
- **One MCP package has 3,226 un-imported sibling calls**
  (`src/lib/nogc_async_mut/mcp`, 315 distinct (file,symbol) pairs, e.g. `jp`
  called 455x). That is a single directory. `src/lib/gc_async_mut/gpu/engine2d`
  has 1,044; `src/lib/common` 864; `src/lib/common/crypto` 613.
- `src/app/lsp` produces a **three-way** spelling split (four with
  `src/app/lsp.handlers`), leaving `lsp_json.spl` and `server.spl` disjoint.
- `src/compiler/10.frontend/core/interpreter` would be the largest exposure of
  all (1,475 calls / 369 pairs) but is currently **excluded from compilation**
  (`driver_source_loading.spl:620,655`). It becomes live if that exclusion is
  ever lifted.

Recommended shape (from the audit's §5):
1. resolve to a physical path (`rt_path_absolute`/`realpath`) *before* deriving
   the module name — noting the four-copies constraint at
   `driver_source_loading.spl:56-62` (`llvm_module_name_from_entry_path`,
   `hir_module_logical_name_from_path`, `bootstrap_mir_logical_module_name`);
   better, hoist the derivation into one shared helper;
2. strip the numeric tier segment once, centrally
   (`compiler.<NN>.<name>. -> compiler.<name>.`), and `std. -> lib.`;
3. keep import spellings as **aliases only**, never competing canonical names;
4. make `resolve_package_sibling_symbols` package-key-based (group by canonical
   physical directory) rather than string-prefix based, or at minimum route its
   prefix through `resolve_module_key` (`module_lowering.spl:543`), which already
   knows the `std.`/`lib.` mapping;
5. extend `_driver_module_name_collision` (`:171-184`) with the inverse check it
   lacks — error when one *physical* file registers under two canonical module
   names with differing package prefixes, catching the split at load time instead
   of as ~530 downstream unresolved names.

### 6.3 Aliased re-export resolution — `export use X.{A as B}`

`T32BridgeResult` (38 errors): `src/app/t32_cli/types.spl:4` does
`export use common.ui.access_cli_grammar.{AccessResult as T32BridgeResult}`, and
consumers then do a normal explicit `use app.t32_cli.types.{T32BridgeResult}`.
The `{X as Y}` rename sub-form of facade re-export does not resolve under native
HIR lowering. Distinct from §3.5 (which was the `export X from M` form, now
fixed) — this one is still open.

### 6.4 The glob transitive-broadening semantics decision — recommendation is REVERT (b)

`glob_transitive_import_broadening_risk_2026-07-27.md` recommends **reverting
mechanism (b)** and **not** adopting the `declaration_count == 0` guard.
Evidence, ranked:

1. **(b) is already gone at HEAD, in a broken state** (§5.1). Whatever is
   decided, that must be repaired; "revert" is the smallest repair.
2. **(b)'s motivating symbol no longer needs it.** The commit message said
   `mir_data` "never re-exports `mir_operand_copy`" — true then, **false at HEAD**:
   `src/compiler/50.mir/mir_data.spl` now exports it twice (`:624`, `:734`).
   Mechanism (a) alone resolves it. The 393-error justification has been
   overtaken by events.
3. **The guard cannot help.** `declaration_count == 0` excludes `mir_data`
   (10 own decls) and `backend_types` (16) — the only two facades where (b)
   mattered — while permitting only 0-decl barrels, which (a) already covers.
   *The guarded option is functionally equivalent to reverting (b), with extra code.*
4. **The residual cost is trivial and better solved declaratively.** Filtering
   mir_data's residual to names actually used by a star-importer with no explicit
   import gives **13 distinct symbols, ~41 use sites, 28 of 98 files**
   (`MirStatic` 6, `MirFieldDef` 6, `MirPlace` 5, `MirConstant` 5, ...). All are
   legitimately part of mir_data's public surface — **one or two added `export`
   lines** fix all 41 sites with zero consumer edits. Smaller than (b)'s 40 lines
   of compiler code, and declarative.
5. **The risk is silent and grows.** 271 capitalized type names are declared in
   more than one module under `src/compiler`; imports are first-write-wins
   (`module_lowering.spl:1368-1370`) with **no duplicate diagnostic**. One active
   collision today (`OptimizationLevel`, `optimization_passes.spl:12` vs
   `backend_types.spl:228`), but the `30.types/*_phase*` shim clusters redeclare
   `HirType`, `Symbol`, `HirExpr`, `Expr` locally and arm a much larger set behind
   a single future refactor toward barrel imports — several of them struct-vs-enum
   kind mismatches, the worst class.

**Keep (a) unchanged** — sweeping an author-declared `export` list is an explicit
promise and carries none of this risk.

The decision must be validated by a **resolution-target** test, not an
error-count test — the error-count metric is what made (b) look good. Proposed
fixture: `B` declares `struct Widget`; facade `A` does `use B.*`; `M` does
`use A.*` **and** declares its own `struct Widget`; assert `Widget` in `M` resolves
to **M's** definition. Fails under (b), passes under revert. It does not exist today.

Also file separately, independent of this decision: `register_imported_symbol`
should warn when a duplicate registration's `SymbolKind` differs from an existing
symbol of the same name. That is the guard that actually addresses the silent-
shadow class.

### 6.5 Deeper star chains — explicitly NOT worth it

`star_import_chain_depth_analysis_2026-07-27.md`: 678 of 765 resolvable
`A -> B -> C` chains have a *theoretical* depth-1 miss. After cross-checking
against the live 1,077-error log and removing false positives (cases where the
erroring module already has a **direct named import** of the same symbol, so
chain depth cannot be the cause), only **2 chains / 6 error occurrences (0.56%)**
are genuinely explained by the depth-1 limitation.

The theoretical surface is inert because 709 of 1,497 files already use direct
named imports. Example of the false-positive class:
`mir_opt._OptimizationPasses.io_passes` shows 89 occurrences for `MirOperand`,
`MirBlock`, `LocalId` — but `io_passes.spl:15-16` already imports all of them
**directly by name**. A symbol already imported by name cannot be unresolved
because of star-chain depth; something else is wrong there.

**Do not make `register_glob_imported_symbols` broadly recursive.** If anything
is done here, it is the narrow zero-declaration-facade case — worth **~6 of
1,077**. Note: one cycle exists
(`hir_lowering.expressions <-> hir_lowering.statements`, verified at
`expressions.spl:11` / `statements.spl:11`), so any recursive implementation
needs a visited set. (Both modules have real declarations, so a
`declaration_count == 0` branch would never fire for that pair.)

### 6.6 Other classified remainders

From `stage4_remaining_error_classification_2026-07-27.md`:

- **Lexer/`TokenKind` family**: 793 total (185 `TokenKind` + 608 across 21 `lex_*`
  symbols). `3eea09c67960` cleared the `lex_*` side for the fixed package; the
  185 `TokenKind` in `compiler.frontend.treesitter.*` remain, pending §6.2.
- **`Mir*` family isolated to `mir_opt/_OptimizationPasses/{engine,io_passes}`**
  (~172): the `mir_data.spl` facade uses bare `export` statements and works for
  many other consumers (`c_backend.spl`, `_CBackendTranslate/*`, `_MirToLlvm/*`).
  Failure looks build-graph/module-inclusion specific to these two files.
  **Needs a probe** before estimating effort.
- **"Untyped function returns a value"** — 166 raw lines / **157 distinct
  (module, function) pairs**, and it is a *mixed bag, not one class*:
  - **85 of 157 (54%) are false positives** — the signature plainly has `-> T`.
    Common thread: generic/nested return types and `me`-receiver methods, e.g.
    `glass_debug.spl:14` `-> List<text>`, `array.spl:93` `-> [[Any]]`,
    `vhdl_hardware_metadata.spl` (11 `me`-methods, all with `-> T`, all flagged).
    One central fix to the return-type-presence check.
  - **72 of 157 (46%) are genuine defects**, e.g. `module_loader.spl:151,495`.
    33 of them cluster in `compression/gzip/*`, which is written untyped
    throughout and needs real annotations, not a bug fix.
- **`json_serialize`** (25) across `app.devhub.adapter_*` — untraced, needs the
  same import-block check as `PrimitiveType`.

---

## 7. Methodology notes for whoever continues

### 7.1 The single most important one: stage-4 HIR errors are invisible without the flag

**Stage-4 HIR errors only appear under `SIMPLE_BOOTSTRAP_STAGE4=1`.** The
non-stage4 lane builds MIR from the flat-AST accumulator
(`bootstrap_lower_to_mir_context`, `src/compiler/80.driver/driver.spl` ~L1107)
and **never surfaces them**. And the flag is **rejected with any entry other than
`src/app/cli/main.spl`**.

Therefore **isolated probes cannot detect this defect class.** Several probes
today compiled and ran correctly while the real build failed. If you write a
minimal repro and it passes, that is not evidence the bug is absent — it is
evidence your repro is in the wrong lane.

Corollary already burned twice: a **seed build** also cannot detect it (§5.5),
because the seed's `Dict.len()` is correct and the defective branches are
unreachable there.

### 7.2 Anchor greps when counting symbol classes

`grep -c 'unresolved name: me'` matched `metal_sffi_*` and manufactured a
phantom "20 residual" class that was chased as real (§4b). Use
`grep -cE 'unresolved name: me$'`. This applies to every short symbol name.

### 7.3 Adding an `rt_*` extern requires a runtime rebuild

Standing rule; it bites silently when a new extern appears to be missing at link
time.

### 7.4 `kill_simple_monitor.shs` will kill your test run at ~60s

`scripts/resource/kill_simple_monitor.shs:148-156` kills any
`is_simple_run_or_test()` match at `CPU_THRESHOLD=95` **and** `MIN_AGE_SECS=60`.
**Both are hardcoded with no env-var override.** Raising `KILL_SIMPLE_MEM_MB` /
`KILL_ANY_MEM_MB` does nothing for this rule — those are RSS guards. Confirmed
live in `/tmp/kill_simple_monitor.log` today (exit 143 at 61-62s, three times):

```
2026-07-27T12:57:09 KILL Killing runaway process pid=2832202 (cpu=95.8% age=60s: bin/simple test)
2026-07-27T12:59:01 KILL Killing runaway process pid=2840507 (cpu=96.1% age=60s: bin/simple test test --whole --mode=interpreter)
2026-07-27T13:01:17 KILL Killing runaway process pid=2904727 (cpu=96.3% age=62s: bin/simple test)
```

**The documented bypass is a lowercase `claude` token in argv.** `is_protected()`
(`:41-59`) does a whole-cmdline glob match against `*claude*`, `*codex*`,
`*tmux*`, `*node*`, `*npm*`, `*daemon*`, the `*_mcp_server` patterns — matched
processes skip **both** the CPU and RSS checks. Precedent:
`doc/03_plan/compiler/bootstrap/cli_selfdelegation_redeploy_plan_2026-07-25.md:44-45`
documents it explicitly, and
`doc/09_report/stage4_bootstrap_memory_ceiling_2026-07-25.md` records a stage-4
build that survived only because `.claude/worktrees/...` appeared in its
`--runtime-path` argument. Concretely:

```sh
ln -sf "$(readlink -f bin/simple)" /tmp/claude_simple_test_runner
/tmp/claude_simple_test_runner test
```

Two further traps:
- **Stage-4 native-build is separately capped at 24 GB RSS** (`:135-138`) — it
  matches `is_simple_run_or_test()`, so it is *not* on the 64 GB generic cap. The
  native-build exemption at `:140-146` skips only the **CPU/age** check, not RSS.
  Three real kills recorded in `doc/03_plan/cert/redeploy_selfhost_plan.md:110-111`.
- **There may be more than one monitor running.** Two instances were live today:
  the pidfile'd one and an **orphaned, untracked** instance (ppid=1, ~66h old).
  `ensure_kill_monitor_running()`
  (`src/lib/nogc_sync_mut/test_runner/system_monitor.spl:610-655`) only checks
  the pidfile, so stopping "the" monitor leaves the orphan still killing things.
- `earlyoom` is a separate, system-wide mechanism this script does not control.

### 7.5 Non-stage4 lane status: AT RISK, but not by this campaign

`nonstage4_lane_regression_check_2026-07-27.md`: the `nostage4.log` exit 1 is
**not** attributable to the HIR fixes. That run reached the backend with
`me=0, unres=0, hir=0` and zero unresolved-name errors; it died on 16 files —
**14** `llvm global load referenced undeclared symbol` (the open bug
`doc/08_tracking/bug/simple_shared_parameter_llvm_global_load_2026-07-17.md`,
whose stated follow-up was never done), **1** 60s compile timeout
(`office/sheets/formula.spl`), **1** ambiguous `to_f32` resolution
(`dom_color.spl`).

Stage 2 and stage 3 were **green** with fix #1 in the tree: each `687 compiled,
0 cached, 0 failed`, linked, and passed bootstrap compiler sanity. Only stage 4
failed.

The genuine risk is **fix #5 (`3eea09c67960`) alone**: it changes
`_driver_module_aliases`, and source loading is **lane-agnostic** — it runs
before the HIR/flat-AST fork, so it changes the module set every stage 2 and
stage 3 build sees. It landed at 22:01, *after* every piece of evidence in that
report. Nothing has exercised it.

**To clear this:** run one `--full-bootstrap` (or stage-2/3-only) at or after
`3eea09c67960` and confirm both stage logs still report `687 compiled, 0 cached,
0 failed` plus `Stage 3 succeeded and passed bootstrap compiler sanity`. One run
covers fixes #2 through #5.

### 7.6 Re-measure at HEAD before trusting any delta

Every error-count delta in §2 describes the tree of the commit that produced it.
Because `69b1b2ab5dc` clobbered `module_lowering.spl` with a stale parallel
version (§5.1), **HEAD's number is unknown**. Establish it — after repairing
§5.3 — before making any further semantics decision.

---

## 8. Latest state — 2026-07-28 (campaign continuation)

Everything below happened after §1-7 were written, in the same tree, roughly
22:57 2026-07-27 through 00:12 2026-07-28 UTC. All shas re-verified as
ancestors of `origin/main` (`git merge-base --is-ancestor <sha> <origin-tip>`)
at the time this section was written. Old figures are kept alongside new ones
so the trajectory stays visible; nothing above is deleted or rewritten.

### 8.1 The parse blocker is fixed — stage 4 now parses clean

`19e2cbf7ec62` (23:52) fixed the actual parse blocker: a multi-line `or`-chain
in `_dup_is_fn_sig` needed parentheses. `958db10638d9` (23:54) pre-emptively
applied the same fix to a second, structurally identical multi-line `and`-chain
in `llm_spawn_rights_are_attenuated`. **This was a source bug, not a parser
bug** — `.claude/rules/language.md` documents "Multi-line booleans — wrap in
parentheses" as a standing rule, and the lexer only suppresses `INDENT` while
`paren_depth > 0`; an unparenthesized multi-line boolean chain falls outside
that suppression window by design.

Result: the current run has **parsed 1,333 files with ZERO parse errors** and
is **800+ HIR modules deep with ZERO unresolved names and ZERO segfaults** —
versus the deterministic segfault at HIR module 32 that stood before this
campaign (§1, §3.1). This is the furthest any Linux x86_64 stage-4 run in this
repo's history has gotten; it is not yet a completed deploy (§8.6).

Note: §5.3 above ("STILL LIVE at HEAD") flagged two undefined-symbol sites
(`register_glob_imported_symbols_depth`, `hir_registry_*`) as the "first task
for the next session," reasoning that a seed build cannot catch them. Given
the current run reports **zero** unresolved names 800+ modules deep, either
those branches were incidentally resolved by the fixes below, or the run
simply has not yet reached the code path that would trigger them. This was
**not independently re-verified** for this update (would require re-grepping
`module_lowering.spl` and `driver.spl` at current HEAD) — treat §5.3's repair
as still open until someone confirms one way or the other.

### 8.2 The `Dict.get()` root fix landed — not just worked around

`7e83e92ce314` (00:04) fixes the actual codegen defect behind
`native_dict_get_struct_value_corrupt_option_2026-07-27.md` (§3.1), which
`9b612a11418c` had only worked around at call sites. Root cause:
`.get()`'s lowering resolved the dict's value type with a single **unguarded**
lookup and, on failure, silently defaulted to `MirType.i64()` — which routed
`decode_runtime_value` into its integer arm, doing `raw >> 3` on what was
actually a struct's heap **pointer**. A miss on that lookup survived testing
because nil shifts harmlessly (looks like "correctly nil" even when the type
resolution failed). Fix: the index-read path's correct logic
(the one `d[k]` already used) was extracted into one shared function now used
by **both** `d[k]` and `.get()`, so the two paths cannot re-diverge again, and
`struct_value_syms` is now propagated through `.unwrap()` as well.

This does not change §3.1's `Dict.len()` finding (`rt_string_len` returning
`-1` for non-string handles) — that defect is unrelated and still open.

### 8.3 Call-site migrations off the broken primitives

Following on from `9b612a11418c`'s workaround pattern (§3.1), four more
migration commits landed:

- `3b69ff27d375` (23:19) — 16 compiler sites moved off corrupt `Dict.get()`.
- `c90e815649d` (00:05) — 33 stdlib sites stopped reading struct-valued Dicts
  through `.get()`.
- `b609117ed51` (23:03) — 33 compiler sites stopped reading `Dict.len()`
  (natively `-1`) at guard/arithmetic sites.
- `f33f5a2d63e6` (22:57) — capped parallel build workers with an explicit
  counter (fork storm fix).

### 8.4 The test suite runs again — and the earlier "resolver bug" theory was wrong

`c1d891341c45` (00:08): two `impl` methods in `test_runner_types.spl`
(`TestFileResult`/`TestRunResult` `is_ok()`) referenced struct fields bare
instead of via `self.` — every other `is_ok()` in the codebase uses `self.`.
Verified post-fix: `Results: 1 total, 0 passed, 1 failed` — the suite-wide
abort is gone (a real failure now surfaces instead of a hard stop).

**Correction:** an earlier working hypothesis that this was a **seed
resolver** bug was wrong. It was a plain bare-field-access source bug in
`test_runner_types.spl`, same class as the many `self.`-omission bugs
documented elsewhere in this campaign — not a compiler defect.

### 8.5 feature-gen and todo-scan fixed; current authoritative totals

- **`bcd46e6b4d36`** (23:53): `parse_csv_fields` in four copies of
  `cli_util.spl` looped `while i < line.len()` over **bytes** while indexing
  by **character** — a classic bytes-vs-chars mismatch. Feature totals are now
  authoritative: **137 total — 95 current, 41 request, 1 blocked, 0 done**,
  with the `implementation` column filled for only 15 of 137.
- **`bd8440d6871a`** (23:21): `todo-scan` now dedupes scanned files by
  realpath. TODO counts were previously inflated by symlinked spellings of the
  same physical file — the same symlink-aliasing failure mode as §2's
  "inflated ~28%" duplicate-reporting finding and §3.3's module-spelling bug,
  just hitting a different tool.

### 8.6 Build-cache correctness and a monotonic-clock bug

`35dbbf8ce852` (00:12), two independent fixes in one commit:

- **Dependency fingerprint now always folded into the build cache key.**
  Previously it was gated behind an env var, so by default a module could
  reuse an object built against a dependency's **old** layout — silently
  wrong binaries. Now always on when the cache is live.
- **Monotonic clock fix.** Two externs used wall-clock `SystemTime` despite
  being named as monotonic clocks, corrupting any latency evidence computed
  from them (wall-clock jumps — NTP steps, suspend/resume — would have shown
  up as bogus latency deltas).

### 8.7 Corrections to the record (2026-07-28 batch)

Same spirit as §4 — these matter more than the wins, because they're exactly
the kind of thing a later session re-derives wrongly if not written down:

- The "residual 20 `me` errors" figure (§4b) is reconfirmed: it was an
  unanchored-grep artifact matching `metal_sffi_*`; the real count is 0.
- **A monitor's `grep -c 'parser_error'` matched the function name
  `parser_error_count`** (not an actual parse-error log line) and falsely
  reported a parse regression. There was no parse regression — see §8.1, the
  current run parses 1,333 files with zero parse errors. Same lesson as §4b
  and §7.2: **anchor the pattern.**
- **The three "theme hard-stop" commits referenced in earlier session
  chatter are NOT unlanded fixes — they are rejected candidates.** All seven
  shas associated with them are **unrecoverable**: they were never pushed,
  having been produced in isolated worktrees that were subsequently discarded.
  Do not spend time on `git show` for them; the objects do not exist at
  `origin/main` or anywhere reachable from it.

### 8.8 Still true — no change

- **No deploy has occurred.** `bin/simple` still resolves to the Rust seed,
  not a self-hosted binary.
- **Linux x86_64 has never had a green stage-4 deploy** in this repo's
  history (§1). Reaching 800+ clean HIR modules (§8.1) is real forward
  progress and the deepest this campaign has gotten, but it is **an
  unfinished milestone, not a completed one** — do not read §8.1 as "stage 4
  passed."

---

## Suggested order for the next session

**2026-07-28 update:** item 1 below (repair §5.3) has **not** been
independently re-verified as still necessary — see the note in §8.1. Confirm
its status first; it may already be moot.


1. **Repair §5.3** (the two live undefined-symbol sites). Static, cheap, no build.
2. **Re-measure the error count at HEAD** under `SIMPLE_BOOTSTRAP_STAGE4=1` with
   entry `src/app/cli/main.spl`.
3. **Fix duplicate-alias reporting (§6.1)** so subsequent counts mean something.
4. **Run one full bootstrap** to clear the §7.5 AT-RISK verdict on fix #5.
5. Then take §6.2 (general canonicalization) — the only fix that scales.

---

## Source index

Working-tree docs:

- `doc/09_report/stage4_remaining_error_classification_2026-07-27.md`
- `doc/09_report/stage4_residual_me_and_text_2026-07-27.md`
- `doc/09_report/glob_transitive_import_broadening_risk_2026-07-27.md`
- `doc/09_report/nonstage4_lane_regression_check_2026-07-27.md`
- `doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
- `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`
- `doc/08_tracking/bug/stage4_me_receiver_unresolved_in_class_methods_2026-07-27.md`
- `doc/08_tracking/bug/stage4_focused_subbuild_star_import_unresolved_2026-07-27.md`
- `doc/08_tracking/bug/hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md` (SUPERSEDED)
- `doc/08_tracking/bug/native_struct_field_map_copy_nilfills_nested_dicts_2026-07-27.md` (INVALID)
- `doc/08_tracking/bug/flat_ast_export_from_and_type_alias_loss_2026-07-27.md`
- `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` (§§4a, 6, 7, 8)

**Recoverable only from git history** (written today, then lost to a sync):

| Doc | Recover with |
|---|---|
| `doc/09_report/stage4_history_timeline_2026-07-27.md` | `git show 014869af28d:<path>` |
| `doc/09_report/kill_simple_monitor_rules_and_test_exemption_2026-07-27.md` | `git show 014869af28d:<path>` |
| `doc/09_report/symlink_module_spelling_sibling_audit_2026-07-27.md` | `git show 42667d47211:<path>` |
| `doc/09_report/star_import_chain_depth_analysis_2026-07-27.md` | `git show 42667d47211:<path>` |
| `doc/09_report/review_stage4_fixes_2026-07-27.md` | `git show 42667d47211:<path>` |
| `doc/08_tracking/bug/module_spelling_symlink_breaks_package_siblings_2026-07-27.md` | `git show ef2b8db2185:<path>` |

Evidence logs (outside the repo, on this host only):

- `/home/ormastes/.claude/jobs/4403a7d8/tmp/stage4_repro24.log` — 1,681 errors (1,942,962 lines)
- `/home/ormastes/.claude/jobs/4403a7d8/tmp/stage4_repro25.log` — 1,077 errors
- `/home/ormastes/.claude/jobs/4403a7d8/tmp/nostage4.log`, `bootstrap.log`
- `/tmp/kill_simple_monitor.log`

Commits:

| SHA | Subject |
|---|---|
| `9b612a11418c` | fix(hir): contains_key + index reads for struct-valued dict lookups (+ 6-commit revert) — the real unblock |
| `67024e9c0a51` | fix(hir): resolve facade re-exports and transitive star imports for glob imports |
| `8af2dc555960` | fix(hir): alias `me` <-> `self` when resolving a receiver identifier |
| `3eea09c67960` | fix(driver): normalize symlink module spellings so package siblings match |
| `e0f6d761320` | fix(parser): support `export NAME from MODULE` re-export form |
| `3721346d70a` | fix(metal_sffi): re-export the quarantine/reap/release submission helpers |
| `86f02c8352c` | docs(bug): me receiver 543 -> 0 correction |
| `69b1b2ab5dc` | "sync gh and push" — the clobber that introduced §5.1 |
| `5dbe1bc31f3` | the only green stage-4 deploy on record (macOS aarch64, 2026-07-25) |
| `19e2cbf7ec62` | fix(easy_fix): parenthesize the multi-line or-chain in `_dup_is_fn_sig` — the real parse blocker (§8.1) |
| `958db10638d9` | fix(os-security): parenthesize the multi-line and-chain in `llm_spawn_rights_are_attenuated` (pre-emptive, §8.1) |
| `7e83e92ce314` | fix(mir): decode `Dict.get()` exactly like the `d[k]` index read — the codegen root fix (§8.2) |
| `3b69ff27d375` | fix(compiler): replace `Dict.get()` call sites that deref a corrupt payload — 16 sites (§8.3) |
| `c90e815649d` | fix(lib): stop reading struct-valued Dicts through `.get()` — 33 stdlib sites (§8.3) |
| `b609117ed51` | fix(compiler): stop reading `Dict.len()` (-1 natively) at 33 guard/arith sites (§8.3) |
| `f33f5a2d63e6` | fix(driver): cap parallel build workers with an explicit counter (§8.3) |
| `c1d891341c45` | fix(test-runner): use `self.` for field access in `TestFileResult`/`TestRunResult` `is_ok()` (§8.4) |
| `bcd46e6b4d36` | fix(cli): parse CSV fields by character index, not byte length — feature-gen fix (§8.5) |
| `bd8440d6871a` | fix(todo-scan): dedupe scanned files by real path (§8.5) |
| `35dbbf8ce852` | fix(build,runtime): monotonic clock externs + dependency-aware object cache key (§8.6) |
