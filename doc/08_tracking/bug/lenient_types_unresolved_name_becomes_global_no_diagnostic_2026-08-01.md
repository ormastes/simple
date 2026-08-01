# lenient_types turns any unresolved name into a global with no diagnostic

- **Date:** 2026-08-01
- **Component:** `src/compiler_rust/compiler/src/hir/lower` (Rust seed HIR lowering)
- **Severity:** systemic diagnostic failure (not a miscompile)
- **Status:** attribution landed; the leniency itself is retained by design

## Symptom

An ordinary typo, or an HIR scope bug, produces **no diagnostic at all** during
compilation and instead fails at **link** time as a bare undefined-symbol name,
thousands of lines from the source, with no file, no line and no function.

## Mechanism (PROVED)

`hir/lower/expr/mod.rs` — under `lenient_types`, a name that resolves to no
local, no callable and no global becomes:

```
HirExprKind::Global(name)  ->  MirInst::GlobalLoad  ->  undeclared LLVM symbol
```

`mir/lower/lowering_expr_ident.rs` emits the `GlobalLoad` keyed by name;
`codegen/instr/mod.rs` and `codegen/llvm/backend_core.rs` resolve that name
against `global_ids`, then `func_ids`, then `use_map` / `import_map` with
`Linkage::Import`. If nothing defines it, the failure is deferred to the linker.

Proved by `undefined_identifier_is_lowered_as_a_global_under_lenient_types`:
lenient lowering of `fn probe() -> i64: return totally_undefined_name`
**succeeds** and the undefined name is present as a `Global`.

Note the strict path is fine — `simple compile --native` on a single file
reports `error: semantic: Undefined("undefined identifier: X")`. The lenient
`native-build` / `native_project` lane is where the signal is lost. This was
already documented at `pipeline/native_project/compiler.rs:130-142`: *"under
`native-build` there is no error at all and the sibling reads an uninitialized
global, which is strictly worse."*

## Two instances that cost significant effort

- `interp_list` — a compiler bug, not a typo. `Expr::If` carries a
  `let_pattern` field that the HIR dispatcher matched with `..` and dropped, so
  `lower_if` never registered the bound name. Fixed in `a1c93dd7167`. The
  interpreter had the identical defect, fixed 2026-07-20; the LLVM/JIT sibling
  was left behind. Instance doc:
  `if_val_expression_binding_lost_hir_2026-08-01.md`.
- `animation_time_ms` — a plain undefined identifier in
  `_simple_web_layout_compose_retained` (21 params, none named that). Instance
  doc: `web_renderer_compose_retained_missing_animation_time_param_2026-08-01.md`.

## Why the leniency was NOT removed (INFERRED from code, PROVED for the
resolution gap)

The fallback is **load-bearing**. `native_project::lower_file` lowers one file
at a time, and `self.globals` is populated only from the current AST module's
own items (`module_lowering/module_pass.rs`); nothing repopulates it afterwards.
A reference to a function, const or enum variant defined in a **sibling file**
is therefore necessarily unresolvable at HIR time and must survive as a `Global`
so codegen can bind it via `use_map` / `import_map`. Making this an error would
break all cross-module compilation.

Enable sites and their stated reasons:

| Site | Reason |
|---|---|
| `hir/lower/mod.rs` (`lower_lenient`) | "bootstrap compilation and backwards compatibility" |
| `pipeline/execution.rs` | gated on `bootstrap_mode`; mirrors the native_project flow |
| `pipeline/native_project/compiler.rs` (`lower_file`) | per-file lowering; cross-module resolution gap |
| `driver/exec_core.rs` | copies lenient mode to align W1006 strictness across lanes |

Git history cannot corroborate the original motivation: `git log -S
"lenient_types"` returns only tree-restore / conflict-repair / hourly-sync
commits, so the introducing commit was squashed away by a VCS incident.

## Fix: attribute, do not reject

`hir/lower/lenient_global_diag.rs` records every name the lenient fallback
lowers to a global, with the file, the enclosing function and that function's
declaration line. `Expr::Identifier(String)` carries no span, so the enclosing
function's line is the tightest attribution available without an AST change —
enough to locate the name.

Compilation behaviour is unchanged. The record is surfaced on
`LoweringOutput.lenient_globals`, with `attributions_for(symbol)` as the
link-failure entry point: given "undefined symbol X" from the linker, it returns
the source locations that emitted it.

All four lenient fallbacks that mint a symbol name are instrumented (the family,
not just the reported member): unresolved identifier, unresolved `@` SFFI
extern, `Type.new` as global, and dotted path.

Per-name printing is level-gated and **default off** (the population is
dominated by legitimate cross-module names, so always-on would be noise):

```
SIMPLE_DIAG_LENIENT_GLOBALS=1
```

## Population census (measured 2026-08-01, base `5ca84bcefe5`)

`compiler/tests/lenient_global_census.rs` (ignored by default):

```
cargo test -p simple-compiler --test lenient_global_census -- --ignored --nocapture
```

Over `src/compiler`, `src/lib`, `src/app`:

| Metric | Count |
|---|---|
| files scanned | 11,380 |
| parsed ok | 11,335 |
| parse failed | 45 |
| lowering failed | 983 |
| distinct names attributed | 2,094 |
| **of those, undefined tree-wide** | **580** |

The 580 are attributed names for which no file in the scanned set defines a
matching function, class, struct, enum, enum variant, extern, type alias, actor
or module-level `val`/`const`/`static`. They cannot be satisfied by any sibling
module, so they are the queue of future link blockers. Rough shape (measured on
the 584-name run below): ~488 lower_snake (function/variable class), ~20
CamelCase, ~14 UPPER_SNAKE.

**580 is a lower bound** — the 983 files that failed lenient lowering and the 45
that failed parsing contribute nothing to the count.

### Validation: the count responds to a real fix (PROVED)

Run twice, on two trees differing only by the landed `interp_list` fix:

| Tree | attributed | undefined tree-wide | `interp_list` present? |
|---|---|---|---|
| `ca8ff9e003d` (predates the fix) | 2,101 | 584 | **yes** |
| `5ca84bcefe5` (fix landed) | 2,094 | 580 | **no** |

On the pre-fix tree the census independently surfaced the known blocker at
`src/compiler/20.hir/hir_lowering/module_surface.spl:240 in
module_surface_from_module` — a live defect located by source line instead of by
link error, which is exactly the intended outcome. On the post-fix tree it is
gone. The metric tracks real defects rather than counting noise.

`animation_time_ms` is **not** present at either commit (the reference in
`simple_web_html_layout_renderer.spl` is a declared parameter here), so that
instance is covered by a shape-equivalent regression test rather than a live
census hit.


## Verification

- `cargo test -p simple-compiler --lib lenient_global_diag` — 10 passed.
- Full `cargo test -p simple-compiler --lib`: 3,443 passed / 115 failed, vs
  baseline 3,433 passed / 115 failed. The 115 failing test **names are
  set-identical** before and after (compared by `comm`); the delta is exactly
  the 10 new tests. No regressions.

## Closing the loop: the linker now consults the attribution (landed)

`attributions_for` existed but nothing called it, so a link failure caused by
this fallback was still a bare symbol name.

The production path could not reach the index at all (PROVED):
`native_project/compiler.rs:532` calls `.lower_module(&ast)`, whose signature is
`pub fn lower_module(mut self, ..) -> LowerResult<HirModule>` — it consumes the
lowerer and returns only the module. Only `lower_module_with_warnings` returns
the `LoweringOutput` that carries `lenient_globals`, and `native_project` never
calls it. Per-file lowering also runs on a spawned thread behind an `mpsc`
channel driven by a rayon pool, with the link running later from `&self`.

So `record_lenient_global` mirrors each entry into a process-global registry in
`lenient_global_diag` — append-only, dedup'd, capped at 100k entries, read only
on the link-failure path — rather than changing three signatures on the
production compile path for diagnostics.
`native_project::linker::link_failure_output` consults it; both native link
paths (`link_objects`, `link_objects_freestanding`) funnel failure text through
that one function. A failure whose symbols were not attributed is left
untouched, so unrelated link errors gain no noise.

Two details worth recording:

- `undefined_symbols_in_linker_output` returns **all** undefined symbols. The
  pre-existing `NativeLinker::extract_undefined_symbol` returns `Option<String>`
  and stops at the first, which would attribute one symbol out of a multi-symbol
  failure. That function is on a different link path and was left alone.
- A lenient unresolved global is by construction absent from `use_map` /
  `import_map` and from `mir.local_globals`, so `mangle` leaves it verbatim and
  the reported name normally *is* the HIR name. `linker_symbol_candidates`
  covers only the residual cases: Mach-O/MSVC leading underscore, the
  `.` ⇄ `_dot_` swap, a `prefix__` module prefix, and the `@` sigil on SFFI
  references.

Verification: 25 tests in `lenient_global_diag` pass (10 pre-existing, 15 new),
including end-to-end cases for both historical blockers — lower the source, then
hand `explain_link_failure` the exact GNU `ld` and LLD wording that shape
produced, and assert the report names the file and the enclosing function. Both
defects are fixed, so both are shape-equivalent regressions. Also covered:
multi-symbol failures, accumulation across separate `Lowerer` instances, and
silence for unattributed symbols.


## Triage of the undefined names (measured at `9a0b9d8ef40`)

Re-running the census at the landed tip gives **578**, not 580 — the tree moved
between `5ca84bcefe5` and `9a0b9d8ef40` (11,294 files scanned vs 11,380, 2,069
attributed vs 2,094). The 578 were classified against definition indexes built
over tiers the census does **not** scan (`src/os`, `src/unit`, `src/type`,
`src/i18n`, `src/hardware`, `src/runtime`), `src/runtime` C exports,
`compiler_rust` exports and registry string literals, and all 3,270 declared
`extern fn` names:

| Class | Count | Meaning |
|---|---|---|
| `UNDEFINED` | 393 | no definition, extern declaration or name-variant anywhere |
| `METHOD_ONLY` | 89 | exists only as an indented (method/nested) definition |
| `PARAM_ONLY` | 28 | exists only as a parameter name somewhere |
| `COMPILER_BUILTIN` | 26 | appears as a string literal in `compiler_rust` |
| `EXTERN_UNBACKED` | 24 | declared `extern fn`, no C/Rust implementation — overlaps the extern-registration backlog |
| `CENSUS_DEF_GAP` | 9 | module-level def *is* in a scanned root; the census def-model missed the form |
| `NAME_VARIANT` | 5 | a prefix variant exists (the `ffi_` / `sffi_` precedent) |
| `OTHER_TIER` | 2 | module-level def in an unscanned tier |
| `EXTERNAL_C` | 2 | defined in `src/runtime` C |

Class counts are INFERRED from static indexes. The two findings below were then
confirmed against real source and are PROVED.

### Confirmed defect class 1: `value` written for `val` (5 sites) — FIXED

`"val" => TokenKind::Val` is in the lexer keyword table; `"value"` has **no**
keyword mapping (PROVED). So `value (a, b) = expr` is not a binding at all — the
names in the parentheses are *reads*, and they become lenient globals headed for
the linker. Tree-wide there are 1,672 `val (`, 11 `var (` and just 5 `value (`:

```
src/app/interpreter/collections/persistent_dict/node.spl:290
src/app/interpreter/memory/refc_binary.spl:409, 468, 550, 551
```

This also demonstrates the "lower bound" claim with a concrete mechanism: of the
ten names bound across those five sites, only `block_size`, `curr_offset` and
`curr_size` reach the census. `k`, `v`, `offset` and `size` are masked because
those names happen to be defined at module level *somewhere else* in the tree,
so `is_defined` clears them even though they are unbound here.

Validated by the same census A/B used for the `interp_list` fix: **578 undefined
before, 574 after** (attributed 2,069 → 2,064). Compared by set, exactly four
names are removed and **none** added — `block_size`, `curr_offset`, `curr_size`
and `_`. The `_` was not predicted: in `value (offset, _) = ..` the wildcard is
read as an identifier too, so the fallback minted a global literally named `_`.
`parse failed` stays at 43, `files scanned` at 11,294 and `lowering failed` at
980, so the edited files still parse.

### Confirmed defect class 2: `enumname_Variant` constructors (63 names) — 61 FIXED, 2 reclassified

63 of the 393 have the shape `lowercase_Capitalized`, e.g.
`binaryopresult_Error`, `predicate_Or`, `selector_Call`, `stmtkind_Expr`,
`concretetype_Array`. `enum BinaryOpResult` with variants
`Int/Float/Bool/String/Error` does exist
(`src/compiler/35.semantics/semantics/binary_ops.spl:16`), and the file defines
lowercase wrappers whose bodies call the capitalized form:

```
fn binaryopresult_error(msg: text) -> BinaryOpResult:
        binaryopresult_Error(msg)
```

Nothing defines or synthesizes `binaryopresult_Error`. No desugar pass generates
`enumname_Variant` constructors. These are unresolved constructor references in
the self-hosted compiler's own source; the language spelling is
`BinaryOpResult.Error(..)`. This is the silent-nil class — worth pairing with
the `check_no_fabricated_extern_definitions` guard, since a weak zero-size
definition would have hidden exactly this.

#### Root cause (PROVED)

A mechanical Rust-to-Simple port artifact. The porter flattened `impl X:` blocks
to free functions (`impl BinaryOpResult { fn int(..) }` -> `fn
binaryopresult_int(..)`) and applied the *same* lowercasing rule to
`Self::Int(v)` / `BinaryOpResult::Int(v)`, which are enum **constructors**, not
methods. The result is a wrapper whose body calls a name nobody defines:

```
fn binaryopresult_int(v: i64) -> BinaryOpResult:
        binaryopresult_Int(v)          # <- minted a lenient global
```

The correct spelling is `BinaryOpResult.Int(v)`. The identical error occurs in
**pattern** position (`type_Simple(name):` as a match arm), which is why the
class spans both expressions and patterns.

#### Disposition, per name

Resolution was done **per file**, not per name — the same prefix denotes
different enums in different files (`type_*` is the inference `enum Type` in
`src/compiler/30.types/type_system/`, but `parser_types_expr.Type` in
`monomorphize/util.spl`). A name was rewritten only when exactly one enum with
that lowercased name was in scope for that file *and* carried that exact
variant.

- **61 of 63 — spelling fix (disposition a).** Rewritten to `EnumName.Variant`.
  Nullary variants drop the empty parens (`type_Bool()` -> `Type.Bool`), matching
  the 28 pre-existing `Type.Bool` uses and zero `Type.Bool()` uses in the
  pristine tree.
- **2 of 63 — `type_Simple`, `type_Pointer`: NOT a spelling error (reclassified,
  filed below).** Both occur only in `src/compiler/40.mono/monomorphize/util.spl`,
  which does `use compiler.frontend.parser_types_expr.{Type, Expr}`. In that
  module `Type` and `Expr` are **structs** (`parser_types_expr.spl:23` and `:204`),
  not enums; the variant sets live on `TypeKind` and `ExprKind`. `Simple`,
  `Pointer`, `UnitWithRepr` and `TypeBinding` exist on **neither**. The file is a
  stale port matching against an AST type model that was removed. Rewriting these
  to any existing variant would trade a link error for a silent wrong answer, so
  they are left loud and filed as a separate defect.

The sweep covered the whole family, not just the 63: the census masks any name
that collides with a module-level definition elsewhere, so a direct source scan
found **125** unresolved `enumname_Variant` names over 361 sites, a strict
superset containing all 63. All 342 sites that resolved to a unique in-scope
enum+variant were rewritten (341 token replacements over 26 files). The other 19
sites are the 17 `util.spl` dead-model sites and 4 occurrences inside comments,
all deliberately untouched.

#### Validation (PROVED, census A/B at base `eada96016e2`)

| Metric | before | after |
|---|---|---|
| files scanned | 11,294 | 11,294 |
| parse failed | 43 | 43 |
| lowering failed | 980 | 980 |
| distinct names attributed | 2,064 | 2,003 |
| **undefined tree-wide** | **574** | **513** |

Compared by set: exactly **61 names removed, 0 added**. `parse failed`,
`lowering failed` and `files scanned` are unchanged, so every edited file still
parses and lowers.

True-positive control: `type_Simple` and `type_Pointer` are **still reported**
after the rewrite. Had the edit merely made the census blind to the
`lowercase_Capitalized` shape, those two would have disappeared as well. The
detector is still live on exactly this class.

Note the 574 baseline, not the 578 quoted earlier in this document: 578 was
measured before the `value (`-for-`val (` fix landed, and this section's A/B is
based on the tip that already carries it.

**Credit split after rebasing onto `50019920d61`.** While this A/B was running, a
parallel lane deleted five files as dead code
(`bidirectional.spl`, `expr_infer.spl`, `expr_infer_calls.spl`,
`expr_infer_ops.spl`, `module_check.spl` under `30.types/type_system/`) and
gutted `checker.spl`. Those edits of mine were dropped rather than resurrecting
deleted files. Of the 61: **51 are fixed by this change** at the landed tip, and
**10 were resolved by that deletion instead** (`infermode_Check`, `type_Bool`,
`type_Borrow`, `type_BorrowMut`, `type_Dict`, `type_Float`, `type_Int`,
`type_Named`, `type_Nil`, `type_Unit`). Either way all 61 are gone; the A/B table
above is the measurement at its own base `eada96016e2` and is not re-attributed.
`checker.spl` was re-derived from the new upstream blob, not from the pre-rebase
local copy.

### Filed: `monomorphize/util.spl` matches enum patterns against structs

Separate defect, NOT fixed here. 17 sites across 13 lines in
`src/compiler/40.mono/monomorphize/util.spl` destructure `Type` and `Expr` as if
they were enums:

```
src/compiler/40.mono/monomorphize/util.spl:31,157,328,374   type_Simple
src/compiler/40.mono/monomorphize/util.spl:65,216,362       type_Pointer
src/compiler/40.mono/monomorphize/util.spl:268              type_UnitWithRepr
src/compiler/40.mono/monomorphize/util.spl:276              type_TypeBinding
src/compiler/40.mono/monomorphize/util.spl:92               expr_Integer, expr_TypedInteger
src/compiler/40.mono/monomorphize/util.spl:95               expr_Float, expr_TypedFloat
src/compiler/40.mono/monomorphize/util.spl:98               expr_Bool
src/compiler/40.mono/monomorphize/util.spl:101              expr_String, expr_TypedString, expr_FString
```

The file is a port of `rust/compiler/src/monomorphize/util.rs`, whose `Type` was
an enum with `Simple`/`Generic`/`Pointer`/... The Simple AST since moved to
`struct Type` carrying a `TypeKind`, and none of these variant names survive on
`TypeKind`/`ExprKind`. The file is not dead — `type_uses_param`,
`infer_concrete_type`, `ast_type_to_concrete` and `concrete_to_ast_type` all have
external callers, and `monomorphize/__init__.spl:99` re-exports from it. Fixing it
means porting the four functions onto `ty.kind` / `expr.kind` plus the current
`TypeKind`/`ExprKind` variant sets, which is a semantic port, not a rename.


## Follow-ups (not done here)

- `Expr::Identifier` has no span, so attribution is function-granular. Giving
  identifiers a span would make it line-exact.
- The `enumname_Variant` class is done (61 rewritten, 2 reclassified and filed).
  Census now stands at **513**. Next in priority order: the 116 names ending in a
  collection-op suffix (`_push`/`_len`/`_get`/`_contains`/…), then the long tail.
- Port the four `monomorphize/util.spl` functions onto the current
  `struct Type` + `TypeKind` / `struct Expr` + `ExprKind` model (section above).
- The census masks any unbound name that collides with a module-level
  definition elsewhere in the tree, so it is a lower bound for a second reason
  beyond the 980 lowering failures and 43 parse failures.
- The pure-Simple compiler mirrors the seed's lenient branch
  (`src/compiler/20.hir/hir_lowering/types.spl`) but has no equivalent
  attribution; instrumenting that side would close the same loop for the
  self-hosted lane.
