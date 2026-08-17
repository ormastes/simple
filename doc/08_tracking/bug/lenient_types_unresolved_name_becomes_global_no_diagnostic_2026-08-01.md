# lenient_types turns any unresolved name into a global with no diagnostic

- **Date:** 2026-08-01
- **Component:** `src/compiler_rust/compiler/src/hir/lower` (Rust seed HIR lowering)
- **Severity:** systemic diagnostic failure (not a miscompile)
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).

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


### Confirmed defect class 3: collection/text methods written as free functions (`X_op(X, …)`)

The next-largest cluster after the enum constructors. The same mechanical
Rust-to-Simple porter that produced `enumname_Variant` also flattened **method
calls** on locals: `tokens.push(t)` became `tokens_push(tokens, t)`,
`input.chars()` became `input_chars(input)`, `graph.keys()` became
`graph_keys(graph)`. The receiver survives as the *first argument*, so the whole
family has one machine-checkable shape:

```
(?<![.\w@"])([a-z][a-z0-9_]*)_([a-z][a-z0-9_]*)\(\s*\1\s*[,)]
```

i.e. `NAME_METHOD(NAME, …)` where the first argument is literally the prefix.

#### Root cause (PROVED, by same-line self-contradiction)

Two sites carry the correct and the broken spelling in the *same expression*:

```
src/compiler/40.mono/monomorphize/cycle_detector.spl:389
    if result_len(result) == all_nodes_keys(all_nodes).len():

src/compiler/70.backend/backend/common/expression_evaluator.spl:137
    Ok(value_int(lhs.as_int() + rhs_as_int(rhs)))
```

`.len()` and `.as_int()` are used correctly on one operand and mis-ported on the
other. Nothing defines `result_len`, `all_nodes_keys` or `rhs_as_int`.

#### Scope of the family (PROVED by direct scan)

Direct scan of `src/compiler`, `src/lib`, `src/app` at base
`dfe952d0afaec367d06e95f3025daaab6f542de6`: **2,961** occurrences of the shape,
**925** distinct names; after removing every name with a module-level definition
anywhere in the tree, **179 names over 289 sites in 40 files** remain unresolved.
The census (which cannot see names masked by a same-spelling definition
elsewhere) reports a subset of those.

A measurement bug caught during this work, recorded because it is the exact
false-clear the campaign keeps hitting: the first definition index matched
`^(fn|class|…)` and therefore **missed every `pub fn`** — 5,289 names. It made
`theme_id_key` (12 sites) look undefined when it is `pub fn theme_id_key` on
line 77 of the very file that calls it. Anchor definition greps on the
visibility modifier, not just the keyword.

#### The naive rewrite is NOT always safe (PROVED by runtime probe)

`X_op(X, a)` → `X.op(a)` is only correct when `X.op` actually exists. Probing
each spelling this cluster implies, against the deployed seed
(`bin/simple run`), found three that do **not**:

| Spelling | Probe result | Verdict |
|---|---|---|
| `d.get(k)`, `d.contains(k)`, `d.contains_key(k)`, `d.keys()`, `d.values()`, `d.remove(k)` | correct | safe |
| `l.push(v)`, `l.len()`, `l.pop()`, `l.reverse()` | correct | safe |
| `t.chars()`, `t.lines()`, `t.trim()`, `t.is_empty()` | correct | safe |
| **`d.get(k, default)`** | hit returns `<special:11>`; miss returns the unresolved-symbol error | **UNSAFE** |
| **`d.items()`** | `Runtime error: Function 'Dict.items' not found` | **UNSAFE** |
| **`t.clone()`** | `Runtime error: Function 'str.clone' not found` | **UNSAFE** |

Rewriting to any of the three bottom rows would have replaced a loud link error
with a corrupt value or a runtime dispatch gap. 11 sites were excluded on this
evidence — see "left loud" below. Probe source: `probe/p2.spl` shape, run with
the seed `bin/simple`; the two-argument `get` is the same defect family as
`doc/07_guide/language/dict_native_pitfalls.md`.

#### Disposition

Rewritten only where the receiver's type is provable from a local declaration, a
parameter annotation, or a same-file initializer whose type is itself provable,
**and** the method is on the safe list above: **134 token replacements over 21
files**, covering 73 names the census reported.

Deliberately left loud (disposition d — a loud link error beats a silent wrong
answer):

- `visited_get` ×3, `rec_stack_get`, `in_degree_get` (3-arg form) — would become
  `d.get(k, default)`, which returns garbage.
- `in_degree_items`, `vars_items` — would become `d.items()`, which does not exist.
- `cycle_path_clone` ×2, `new_to_clone` ×2 — would become `t.clone()`, which does
  not exist.
- `queue_pop` (`cycle_detector.spl:374`) — the call site is
  `match queue_pop(queue): Some(v) / None`, so it expects an `Option`. `l.pop()`
  returns the element, not an `Option`; rewriting would leave a `match` that
  never binds. Fixing this needs the surrounding match restructured, which is a
  semantic change, not a spelling fix.
- The remaining 148 sites whose receiver type this lane could not prove
  (`rhs_as_int` ×11, `rng_next_range` ×7, `block_def_parse_payload` ×4,
  `reader_result_is_err` ×4, …) and 15 whose method provably does not exist on
  the named class (`fs_has_file` ×3, `metadata_add_circular_error`,
  `metadata_add_circular_warning`, `result_add`, `checker_check_call`, …). The
  second group is the more interesting one: those are missing *methods*, i.e.
  real gaps, not spellings.

#### Validation (PROVED, census A/B at base `dfe952d0afaec367d06e95f3025daaab6f542de6`)

Note the baseline is **463**, not the 513 quoted earlier in this document: 513
was measured at `eada96016e2` and other lanes have landed since.

| Metric | before | after |
|---|---|---|
| files scanned | 11,286 | 11,286 |
| parse failed | 43 | 43 |
| lowering failed | 979 | 979 |
| distinct names attributed | 1,948 | 1,880 |
| **undefined tree-wide** | **463** | **395** |

Compared by set: exactly **68 names removed, 0 added**. `files scanned`,
`parsed ok` (11,243), `parse failed` and `lowering failed` are all unchanged, so
every edited file still parses and still lowers. Five of the 73 census-visible
names touched remain, because each has a further site this lane could not prove
(`env_contains`, `errors_len`, `expected_errors_len`, `in_degree_get`,
`tokens_len`).

**True-positive control.** Eleven names of the *identical* `X_op(X, …)` shape
were deliberately left unfixed, nine of them in `cycle_detector.spl` — the file
that received 34 of the 134 replacements. After the rewrite they are **still
reported**: `visited_get`, `rec_stack_get`, `in_degree_get`, `in_degree_items`,
`vars_items`, `cycle_path_clone`, `new_to_clone`, `queue_pop`, `to_clone`,
`metadata_add_circular_error`, `metadata_add_circular_warning`. Had the edit merely blinded the
census to this name shape, they would have disappeared with the rest. The
detector is still live on exactly this class inside an edited file.


### Confirmed defect class 4: mangled float literals — `0[0]` written for `0.0` — FIXED

Same porter, different mechanism, and the worst of the four: this one is a
**silent wrong answer**, not a link error.

#### Root cause (PROVED)

The porter translated Rust **tuple-field access** `x.0` into Simple index syntax
`x[0]` — a correct rule — and then applied it to *any* `<digits>.<digits>` token,
including float literals and version numbers in prose. `0.0` became `0[0]`: a
valid-parsing index expression on the integer literal `0`.

The mechanism is visible in the wild at `vulkan_backend.spl:99`, where a
porter-generated tuple temporary `_tup_0` and a mangled comment `# Vulkan 1[3]`
sit on the same line.

This predicts the family exactly, and the prediction was checked: no other shape
exists. Scans for `1[0]f64`-style suffixed literals, trailing-dot `1[]`, and
chained `1[2][3]` all return **zero** hits across `src/**`. Leading-dot floats
(`.5`) cannot occur because Rust's grammar does not accept them.

#### What `0[0]` actually evaluates to (PROVED, per engine)

Measured with the `x86_64-unknown-linux-gnu` binary copied to a scratch name,
via `SIMPLE_EXECUTION_MODE`:

| engine | result |
|---|---|
| `interpreter` | **fails closed**: `error: semantic: invalid operation: cannot index value of type i64` |
| `jit` (and default) | garbage denormal ~`1.5e-322`, **identical for `0[0]`, `1[0]` and `0[0001]`**; `== 0.0` is false, `!= 0.0` is true |
| `--native` | prints as `0.0` but `== 0.0` is **false** and `!= 0.0` is **true** |

So on JIT and native every `<int>[<int>]` literal collapses to the *same*
not-equal-to-anything value, and any `x != <mangled>` test is **constant true**.
Note the engine split: the interpreter would refuse to load these modules at all,
so this defect also blocks any interpreter-driven self-host path.

#### Blast radius (PROVED by RED/GREEN on the real function body)

A harness wrapping `binaryopsemantics_eval_float_float` verbatim (lines 128–154)
with a local `BinOp` enum:

```
RED  (mangled):  And(0.0,0.0) = Bool(true)   Or(0.0,0.0) = Bool(true)
GREEN (0.0):     And(0.0,0.0) = Bool(false)  Or(0.0,0.0) = Bool(false)
```

GREEN reproduces on both `jit` and `interpreter`. Per site:

- `binary_ops.spl:148-151` — float `and`/`or`/`AndSuspend`/`OrSuspend` returned
  **`true` for every input pair**. Float truthiness was a constant.
- `cast_rules.spl:95` — bool→float cast returned the **same garbage for `true`
  and `false`**; the branch distinction was destroyed entirely.
- `cast_rules.spl:117` — float→bool returned `true` for **every** float,
  including `0.0` and `-0.0`.
- `testing.spl:381` — the epsilon in approximate float equality became ~`1.5e-322`
  instead of `1e-4`, so float `assert_equal` reported "not equal" for any
  non-identical pair.
- `escape.spl:265` — `stack_allocation_ratio()` returned garbage instead of `0.0`
  on the zero-allocations path.

**This is a behaviour change.** Any code that relied on float `and`/`or` being
unconditionally true, or on float→bool always being true, will now see correct
results and may change outcome. That is intended.

#### Enumeration and discrimination method

Scan: `git grep -nE '(^|[^]A-Za-z0-9_.)])[0-9]+\[[0-9]+\]'` over `src`. The
leading class excludes an identifier, `.`, `)` or `]` before the digits — i.e. it
keeps only an **integer-literal receiver**. Real indexing always has an
identifier, call, or subscript receiver (`_for_item_3[0]` in the very same
`escape.spl` is correctly excluded), so receiver kind is a sound discriminator.

Note the bracket expression must be written `[^]A-Za-z0-9_.)]` with `]` first —
POSIX brackets do not honour `\]`, and the escaped form silently matches nothing.
An earlier attempt returned 0 hits for this reason.

Results: **71 raw hits**; 51 in `src/compiler_rust/vendor/**` (out of owned-code
scope, and all genuine Rust tuple/array indexing); **20 owned `.spl` lines**.

Of those 20, exactly **1 false positive**: `riscv_rvv.spl:141`, where `1[25]` and
`010[14:12]` are legitimate RVV bit-field notation inside a comment. **False
positive rate 1/20 = 5%** on owned code. No mangled site was missed by the filter
and no real index expression was rewritten.

#### Disposition, per site

Executable, value-changing — **fixed**:

| site | was | now |
|---|---|---|
| `binary_ops.spl:148-151` | `0[0]` ×8 | `0.0` |
| `cast_rules.spl:95` | `1[0]`, `0[0]` | `1.0`, `0.0` |
| `cast_rules.spl:117` | `0[0]` | `0.0` |
| `escape.spl:265` | `0[0]` | `0.0` |
| `testing.spl:381` | `0[0001]` | `0.0001` |

Executable but inside a string literal (wrong user-facing text, not a wrong
value) — **fixed**: `validators.spl:180` `"version 3[35]+"` → `"3.35+"`.

Comment/docstring prose, zero runtime risk — **fixed** because two of them
document the very semantics at issue: `cast_rules.spl:91-92`
(`1 or 1[0]` / `0 or 0[0]`), `truthiness.spl:17` (`` `0[0]` (float) ``),
`validators.spl:77,128` (`Phase 2[2]`), `parser_types.spl:92` (`Phase 3[3]`),
`backend_helpers.spl:160` (`2[5]x`), `vulkan_backend.spl:99` (`Vulkan 1[3]`).

**Left alone (false positive):** `riscv_rvv.spl:141` — bit-field notation, not a
float. Rewriting it would have corrupted a correct encoding comment.

No regex sweep was used; every site was edited by line number after reading its
receiver.

### Confirmed defect class 5: the `X_op(X, …)` residue whose receiver IS provable

The previous lane left 148 sites of this shape as "receiver type unproven" and
15 as "method provably does not exist". Re-deriving the family at base
`e4b4561c803` gives **106 unresolved names over 154 sites in 37 files** (direct
scan; the definition index is anchored on the visibility modifier so `pub fn` is
not missed).

Most of the 148 are in fact provable, by three kinds of evidence that need no
type checker:

1. **Same-expression binding.** `expression_evaluator.spl:132-133` binds `lhs`
   and `rhs` from the *identical* expression `self.eval_expr(_, ctx)?`. Eight
   lines then call `lhs.as_int()` and eleven call `rhs_as_int(rhs)`. Whatever
   `lhs` is, `rhs` is. The file does `use compiler.backend.backend_types.*`,
   where `Value.as_int() -> i64` is defined (`backend_types.spl:344`).
2. **Same-file self-contradiction on the same variable.**
   `module_loader.spl:216` calls `reader_result_is_err(reader_result)` while
   line 217 calls `reader_result.unwrap_err()` — one line apart, same variable.
   `linker_wrapper_lib_support.spl:86-88` uses `add_result.is_err()` /
   `.unwrap_err()` correctly, while line 344 uses the broken spelling on a
   sibling `Result`; lines 356 and 387 use `libraries.len()` / `resolved.len()`
   correctly while 349 and 380 use `libraries_len(libraries)`.
   `testing.spl:114-115` uses `expected_errors.len()` and `errors.len()`
   correctly; line 118 uses `expected_errors_len(expected_errors)`.
3. **Explicit parameter annotation plus a class that carries the method.**
   `check_macro_in_hir(checker: MacroChecker, …)` at `macro_check/mod.spl:258`,
   and `MacroChecker.check_call` at `:173`.

**Correction to the previous lane's triage.** `checker_check_call` was listed
among the 15 names whose "method genuinely does not exist on the named class".
It does exist — `MacroChecker.check_call(call: MacroCall) -> MacroCheckResult`,
`macro_check/mod.spl:173` — and the receiver is an explicitly annotated
parameter, so it is the single most provable site in the whole cluster. The
other 14 in that group survive re-checking (see "left loud" below).

#### A trap found by probe: `Result.value` is NOT the accessor

`linker_wrapper_lib_support.spl` and `module_loader.spl` carry a **second**
porter shape — a bare identifier `X_result_value` (not a call) standing in for
Rust's `.unwrap()`:

```
val libraries = lib_result_value          # undefined identifier
```

The obvious rewrite is `lib_result.value`. Probed against the seed
(`bin/simple run`), that returns `<value:0x1800000007>` for an `Ok(7)` — a raw
tagged pointer, **not** `7`. `.unwrap()` returns `7`. Rewriting to `.value`
would have replaced a link error with a silent wrong answer. All eight sites
use `.unwrap()`.

#### Probe results (PROVED, seed engine, `bin/simple run`)

| Spelling | Result | Verdict |
|---|---|---|
| `r.is_err()`, `r.is_ok()`, `r.unwrap()`, `r.unwrap_err()` on `Result` | correct | safe |
| `i.to_string()` / `f.to_string()` / `b.to_string()` (i64/f64/bool) | `42` / `1.5` / `true` | safe |
| `t.trim()`, `t.trim_start()`, `t.replace(a,b)`, `t.len()`, `t.contains()`, `t.starts_with()` | correct | safe |
| `l.len()`, `l.is_empty()`, `l.map(f)`, `l.contains(v)` | correct | safe |
| **`r.value` on `Result`** | `<value:0x1800000007>` for `Ok(7)` | **UNSAFE** |

#### Disposition

**75 token replacements over 10 files**, every one a line-for-line identifier
rewrite (`75 insertions(+), 75 deletions(-)`; no structural change):

| file | sites |
|---|---|
| `70.backend/linker/linker_wrapper_lib_support.spl` | 15 |
| `15.blocks/blocks/testing.spl` | 13 |
| `70.backend/backend/common/expression_evaluator.spl` | 11 |
| `99.loader/loader/module_loader.spl` | 10 |
| `35.semantics/macro_check/mod.spl` | 9 |
| `15.blocks/blocks/text_transforms.spl` | 5 |
| `15.blocks/blocks/highlighting.spl` | 4 |
| `20.hir/inference/serialize.spl` | 4 |
| `35.semantics/semantics/cast_rules.spl` | 3 |
| `35.semantics/macro_check/template.spl` | 2 |

#### Validation (PROVED, census A/B at base `e4b4561c803`)

| Metric | before | after |
|---|---|---|
| files scanned | 11,284 | 11,284 |
| parsed ok | 11,241 | 11,241 |
| parse failed | 43 | 43 |
| lowering failed | 979 | 979 |
| distinct names attributed | 1,880 | 1,838 |
| **undefined tree-wide** | **395** | **353** |

Compared by set: exactly **42 names removed, 0 added**. All four harness
constants are unchanged, so every edited file still parses and still lowers and
the delta is comparable. The removed set is *identical* to the predicted set —
no collateral removals and no misses (`comm` both directions empty).

42, not 75, because the census masks any unbound name that also exists as a
module-level definition somewhere else in the tree. `rhs_as_int` (11 sites),
`reader_result_is_err`, `code_result_is_err`, `reader_result_value` and
`code_result_value` are all masked that way and were fixed without moving the
count. This is the documented lower-bound effect, measured again here.

**True-positive control.** Five names of the *identical* `X_op(X, …)` shape were
deliberately left unfixed **inside files that were edited** — `value_type_name`
(`testing.spl`, 13 replacements), `vars_items` (`text_transforms.spl`, 5),
`target_is_float` (`cast_rules.spl`, 3), and `kind_to_text` + `kind_can_follow`
(`template.spl`, 2). After the rewrite all five are **still reported**. Had the
edit merely blinded the census to this name shape, they would have disappeared
with the rest. The detector is still live on exactly this class inside edited
files.

A sixth intended control, `scope_get`, turned out to be **invalid**: it is not
in the *before* list at all, because some other module defines a `scope_get`
that masks it. A control has to be verified present in the baseline before it
can prove anything — an absent name "still absent" proves nothing.

### New defect class: porter emitted `if`/`while` with an EMPTY body

Strictly worse than the link-error family, and the census **structurally cannot
see it** because no name is left unresolved. Filed here; **assigned to a
separate lane, not fixed by this one.**

`capability_tracker.spl:70-84`:

```
for inst in self.instructions:
    if backend == "cranelift":
        if inst.cranelift:
        supported = supported + 1
```

The inner `if` has no body, and `supported = supported + 1` is dedented to the
inner `if`'s own level, so it executes for **every** instruction: the
"supported instructions" count always equals the total instruction count, on
every backend. Four sites in that one function, one per backend.

Same shape in `effects.spl:117-119`, where the porter flattened Rust's
`if let Some(v) = x { if v.is_async() {`:

```
val callee_effect = env_get(env, callee)
if callee_effect.?:
    if callee_effect_value_is_async(callee_effect_value):
    return Effect.Async
```

`return Effect.Async` fires for any callee present in `env`, async or not, so
`infer_function_effect` reports `Async` for every function that calls anything
it knows about. `callee_effect_value` is also a phantom binding the porter never
emitted.

**Enumeration.** A line matching `^(\s*)(if|while|for|elif)\b.*:\s*$` whose next
non-blank, non-comment line is indented **at or below** the opener, with
per-file docstring tracking: **29 sites in 8 files**, all under `src/compiler`:

```
src/compiler/10.frontend/parser/recovery.spl              8
src/compiler/70.backend/backend/capability_tracker.spl    4
src/compiler/30.types/type_system/effects.spl             4
src/compiler/90.tools/text_diff.spl                       3
src/compiler/35.semantics/macro_contracts.spl             3
src/compiler/20.hir/inference/serialize.spl               3
src/compiler/55.borrow/gc_analysis/barriers.spl           2
src/compiler/00.common/dependency/resolution.spl          2
```

Two measurement bugs caught while enumerating it, both recorded because they are
the exact false-clear/false-alarm pair this campaign keeps hitting:

- **False positives, 46 → 29.** Without docstring tracking the scan returns 46;
  17 of those are `if` lines inside `"""` example blocks (e.g.
  `crypto_ffi.spl:141`, which is prose, not code).
- **False *negatives*, 21.** A first docstring filter leaked its in-docstring
  flag **across files** — the `next` branches skipped the per-file reset — which
  silently dropped both of the files whose sites had already been read and
  confirmed real, and returned 21. Reset parser state on **filename change**,
  not at EOF. A filter that removes noise can remove signal by the same edit;
  the tell was that a verified-real site disappeared.

Restoring the intended nesting is a semantic port, not a rename, and each site
needs its Rust original consulted — hence not fixed here.

#### RESOLVED `3473612bd37` — and the severity above is partly WRONG

Re-derived count: **36 `if` sites in 9 files** (not 29 in 8). The delta is
entirely `recovery.spl` (14, not 8) plus `cycle_detector.spl:191`, which the
first scan missed. One further hit, `exhaustiveness_validator.spl:357`, is a
**false positive**: its body is a `"""…"""` string in value position, i.e. the
docstring trap again, in the opposite direction — stripping docstrings before
the emptiness test turns a legitimate string-valued body into a phantom hit.
Seven `case` arms are also body-less and all seven are deliberate no-ops
(`module_loader.spl` documents its two as fall-throughs). No empty `while`,
`for`, `else`, or `elif` body exists anywhere in `src/`.

**The stated behaviour was never measured, and it is not what happens.** PROVED
by probe on the seed engine, with a sabotage arm that discriminates all three
shapes:

| shape | behaviour |
|---|---|
| empty `if`, **1** following statement | statement is **absorbed as the body** — accidentally CORRECT |
| empty `if`, **n** following statements | statement 1 absorbed; **2..n run unconditionally** |
| empty `if` in **value position** | yields nil on the (outer-true, inner-false) path; following `elif`/`else` arms are **dead** |

So `capability_tracker.spl` did **not** report every instruction as supported.
Hand-computed 1-of-4 cranelift / 2-of-4 llvm inputs returned 25 / 50 both before
and after the fix. Likewise `effects.spl:117` is single-statement and was already
equivalent to the conjunction. Both were re-nested as hardening only.

The genuinely wrong sites were:

| site | wrong because | behaviour change |
|---|---|---|
| `resolution.spl:134` | value position | `resolve(file, !dir)` returned nil, not `Unique(File)`; `elif file_exists` was dead. **PROVED** (probe returned `0`) |
| `serialize.spl:154` | value position | `trim_quotes` returned nil for any unquoted string of length ≥ 2 |
| `effects.spl:355` | value position | `needs_await` returned nil, not `AwaitMode.None`, for a known sync callee |
| `barriers.spl:200` | value position | Generational arm returned nil when target is GC and source is not |
| `text_diff.spl:60,65` | 3 and 2 statements | LCS backtrack decremented `i`/`j` regardless of whether the lines matched |
| `resolution.spl:153` | 3 statements | `__init__.spl` skip did not skip the check it guards |

**The fix is condition merging, not re-indentation.** The Rust originals show the
porter flattened a single conjunction (`current.lexeme == "def" && matches!(…)`,
`i > 0 && j > 0 && old[i-1] == new[j-1]`) into nested `if`s. Naive re-indentation
of the `text_diff` backtrack would have made it **loop forever** rather than
return a wrong answer — a nesting restoration done by shape alone is a hazard.

Left unfixed for want of provable intent: the unresolved names themselves
(`has_current_lines`, `effect_value_is_async`, `callee_effect_value`, …) stay
loud; `macro_contracts.spl`'s `inject` arm carries a TODO because the Rust
original populates `inject_labels`/`injections` and the Simple port rebuilds
`result` from itself, so nesting alone cannot restore the data flow.

Not verified: the **pure-Simple** parser's recovery. Both `bin/simple` and
`bin/release/x86_64-unknown-linux-gnu/simple` are the Rust seed (enum-probe = 0),
so every runtime claim above is seed-engine evidence. If the self-hosted parser
does not absorb the first statement, the 32 "accidentally correct" sites were
broken there too — which is a further argument for the merge that landed.

## Follow-ups (not done here)

- `Expr::Identifier` has no span, so attribution is function-granular. Giving
  identifiers a span would make it line-exact.
- The `enumname_Variant` class is done (61 rewritten, 2 reclassified and filed).
- The `X_op(X, …)` method-as-free-function class: the previous lane did 134
  replacements over 21 files; this lane did 75 more over 10 files, taking the
  census from **395** to **353** (measured at `e4b4561c803`). What remains of the
  family is the residue listed under "left loud" below — overwhelmingly *real
  missing methods*, not spellings.
- ~~Fix the 29 empty-body `if`/`while` sites~~ — DONE in `3473612bd37`; the
  re-derived figure was 36 sites in 9 files and the severity was overstated (see
  "RESOLVED" above). Still open from that work: the `macro_contracts.spl`
  `inject` arm is an incomplete port (TODO in place), and the pure-Simple
  parser's empty-block recovery is unverified.
- Provide the missing `std.random_utils` module, or port `fuzz.spl` onto an
  existing RNG (see "left loud" below).
- Restore the impl blocks the porter emptied: `NumericType`, `FragmentKind`,
  and the receivers in `escape.spl` / `roots.spl` / `resolution.spl` /
  `hygiene.spl` / `visibility_checker.spl`. These are the *real missing
  methods*, and they are now the bulk of what the census still reports.

### Left loud deliberately (disposition d)

A loud link error beats a silent wrong answer. None of these were rewritten to a
plausible neighbouring spelling.

- **`effects.spl` (5 names: `effect_is_sync`, `effect_value_is_async`,
  `effect_value_is_sync`, `callee_effect_value_is_async`, `scc_contains`)** —
  the enclosing `if` bodies are **empty** (new class above). `Effect.is_async()`
  does exist and line 232 of the same file calls it correctly, so the rename
  alone would "work" — and would leave an `if` with an empty body while the
  `return` fires unconditionally. Fixing the name without fixing the nesting
  converts a loud link error into a silent wrong answer. Blocked on that lane.
- **`fuzz.spl`: `rng_next_range` ×7, plus `rng_create`, `rng_next`,
  `random_choice`** — `src/lib/nogc_sync_mut/fuzz.spl:16` does
  `use std.random_utils.{…}` and **no module `random_utils` exists anywhere in
  the tree**; `fuzz.spl` is the only file that mentions `rng_next_range`.
  `src/lib/common/random_pure.spl` exposes an unrelated API (`lcg_*`, scalar
  returns) rather than the `(new_rng, value)` tuple protocol `fuzz.spl` calls.
  A missing module, not a spelling.
  These were also a **false positive of the `X_op(X, …)` scan**: the shape
  matched only because the local happens to be named `rng`, so `rng_next_range(rng, …)`
  looks like a flattened method call. The callee is a genuine free function that
  is merely absent. Any scan keyed on `prefix_method(prefix, …)` will collide
  with real free functions whose first parameter is named after them.
- **`cast_rules.spl` `target_is_float`** — `cast_rules.spl:29` reads
  `# NumericType Methods (was: impl NumericType:)` and the section body is
  **empty**. The porter dropped the whole impl block, so `is_float()` genuinely
  does not exist on this enum. (An `is_float()` does exist in `simd_check.spl`,
  on an unrelated class — rewriting against it would bind the wrong type.)
- **`template.spl` `kind_to_text`, `kind_can_follow`** — identical: the
  `# FragmentKind Methods (was: impl FragmentKind:)` block is empty.
- **`escape.spl`, `roots.spl`, `resolution.spl`, `hygiene.spl`,
  `visibility_checker.spl`** — every one carries `# X Methods (was: impl X:)`
  markers with empty bodies. `pts.add/union/all`, `set.add_root/all_roots`,
  `fs.has_file`, `scope.bind/lookup`, `symbol_table.lookup/get` are real missing
  methods. This confirms and extends the previous lane's 15-name group (minus
  `checker_check_call`, corrected above).
- **`expression_evaluator.spl` `scope_get`** — the receiver is an element of
  `scopes: [[Dict<text, Value>]]`, i.e. a **list**, not a `Dict`, and
  `list.get(i)` has its own known defect. Ambiguous receiver, left loud. (Also
  not census-visible, so it could not serve as a control.)
- **`text_transforms.spl` `vars_items`** — `Dict.items` does not exist
  (previous lane's probe), unchanged. Note the enclosing loop is therefore still
  broken; `result_replace` inside it was still fixed, because that is a strict
  improvement and `vars_items` keeps the defect visible.
- The mangled-float class (`0[0]` for `0.0`) is done: 19 of 20 owned sites
  corrected, 1 left alone as a verified false positive (`riscv_rvv.spl:141`,
  RVV bit-field notation). The vendored Rust hits are out of owned-code scope.
- Give `Dict` an `items()`/`entries()` method and `text` a `clone()`, or decide
  they are deliberately absent; three sites are blocked on that answer.
- Make two-argument `Dict.get(k, default)` either work or fail loudly. It
  currently returns `<special:11>` on a hit and the unresolved-symbol error on a
  miss, while 47 call sites already use it.
- Port the four `monomorphize/util.spl` functions onto the current
  `struct Type` + `TypeKind` / `struct Expr` + `ExprKind` model (section above).
- The census masks any unbound name that collides with a module-level
  definition elsewhere in the tree, so it is a lower bound for a second reason
  beyond the 980 lowering failures and 43 parse failures.
- The pure-Simple compiler mirrors the seed's lenient branch
  (`src/compiler/20.hir/hir_lowering/types.spl`) but has no equivalent
  attribution; instrumenting that side would close the same loop for the
  self-hosted lane.
