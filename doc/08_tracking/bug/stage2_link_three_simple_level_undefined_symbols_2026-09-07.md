# Stage 2 link: three Simple-level undefined symbols (`GenericTemplate.is_err`, `Unit`, `str.split_whitespace`)

**Status:** Diagnosed, NOT fixed (deliberately handed off — see rationale per symbol)
**Observed:** 2026-09-07
**Related fix landed alongside this doc:** the two `rt_file_*_create_excl_no_follow`
Rust-runtime twins that were also undefined at this same Stage 2 link (see
`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs`).

Stage 2's native-build linked against the Rust runtime and failed with five
undefined symbols. Two (`rt_file_copy_create_excl_no_follow`,
`rt_file_link_create_excl_no_follow`) were a missing Rust-runtime twin and are
fixed in this same change. The other three are Simple-level defects in
`src/compiler`, not runtime gaps, and are recorded here instead of fixed —
each is either a multi-file semantic decision or overlaps a already-documented,
actively-worked compiler codegen gap.

## 1. `GenericTemplate.is_err`

**Declared:** `trait CompilationContext` in
`src/compiler/00.common/compilation_context.spl:182`:
```
fn load_template(name: text) -> GenericTemplate?
```
**Used as if it returned `Result<GenericTemplate, text>`:**
`src/compiler/40.mono/instantiation.spl:71-79` (field `context: CompilationContext`
declared at line 39):
```
val load_result = self.context.load_template(template_name)
if load_result.is_err():
    ...
val tmpl = match load_result:
    case Ok(value): value
    case Err(err): ...
```
`.is_err()` / `Ok(..)` / `Err(..)` only make sense for `Result<T, E>`, not for
the trait's declared `GenericTemplate?` (nilable/Option). The sibling trait
method `compile_template` on the very same trait already returns
`Result<TemplateCompiledUnit, text>`, so `load_template`'s `GenericTemplate?`
looks like the odd one out, not a deliberate design choice.

**Why not fixed here:** `grep -rn 'impl CompilationContext'` finds **zero**
concrete implementers anywhere in the tree — this trait is unfinished
scaffolding with a single caller. Changing the trait's return type to
`Result<GenericTemplate, text>` costs nothing today (nothing implements it),
but two different `GenericTemplate` types exist in the tree with the exact
same bare name — an `enum GenericTemplate` in
`src/compiler/40.mono/monomorphize/deferred.spl:35` and the `struct
GenericTemplate` the trait actually references in `compilation_context.spl:99`
— and the undefined symbol is un-qualified (`GenericTemplate.is_err`, no
module path), so a fix must also confirm the mangler disambiguates the two
before or after the signature change, not just make the signature consistent.
That is more than a one-line change and belongs to whoever finishes this
trait's real implementation.

## 2. `Unit`

**Called as a bare zero-arg constructor** at three sites, all as the success
payload of a `Result[Unit, ...]`:
- `src/compiler/80.driver/cache/cas_batch_transaction.spl:148` and `:214`
  (`Ok(Unit())`, function returns `Result[Unit, CasBatchTransactionErrorV1]`)
- `src/compiler/80.driver/action_graph/scc_compile_outputs.spl:175`
  (`Ok(Unit())`)

**No definition backs a callable `Unit`:** `grep -rn 'struct Unit\|class
Unit\|fn Unit\b'` across `src/` returns nothing. The language does have a
built-in unit/void concept — the frontend's `EXPR_UNIT` AST node, whose display
name is `"Unit"` (`src/compiler/10.frontend/core/_AstExpr/accessors.spl:348`)
— but that node is produced by parsing the empty-tuple literal `()`, not by
calling an identifier `Unit(...)`. The three call sites above write `Unit()`
as if `Unit` were a real zero-field struct with a synthesized constructor,
which nothing in the tree provides, so codegen emits a call to a symbol that
is never defined.

**Why not fixed here:** the mechanical fix (`Unit()` -> `()`) is plausible but
unverified — it depends on whether `Result[Unit, E]`'s `Unit` type parameter is
itself resolved as the builtin unit type or as some other synthesized type by
the generic-instantiation machinery, which needs confirmation before touching
three call sites in build-cache/action-graph code.

## 3. `str.split_whitespace`

**Called via method syntax** (UFCS) on `text`-typed receivers at 15+ call
sites, e.g. `src/compiler/80.driver/incremental_builder.spl:57,79,85,91,340,346,352,358`,
`src/compiler/80.driver/shb/shb_extractor.spl:247,254,261,268`,
`src/compiler/90.tools/duplicate_check/_Detector/interner_and_logging.spl:55`,
`src/compiler/80.driver/cache/dirty_module_record.spl:70`.

**Only definition is a plain free function**, not a runtime builtin:
`fn split_whitespace(text: text) -> [text]` in
`src/lib/common/text_advanced.spl:59`.

**Root cause located precisely** in the Rust seed's LLVM backend:
`qualified_runtime_method_owner_is_builtin` in
`src/compiler_rust/compiler/src/codegen/llvm/mod.rs:30` classifies a qualified
method name as "builtin-backed" using ONLY the receiver-type prefix (`str`,
`text`, `Array`, `Dict`, ...), never the specific method (leaf) name. One
caller of that predicate,
`src/compiler_rust/compiler/src/codegen/llvm/mod.rs:107`, correctly guards it
with `&& resolved_text_runtime_method(candidate).is_some()`. The OTHER caller,
`src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2789`
(`qualified_owner_is_user_type = dotted.contains('.') &&
!qualified_runtime_method_owner_is_builtin(func_name)`), does **not** — so any
UFCS method call whose receiver type is builtin (`text`/`str`) is
unconditionally treated as backed by a native runtime shim, even when, as
here, the method (`split_whitespace`) is a genuine pure-Simple free function
with no runtime counterpart. This causes an emitted call to `str.split_whitespace`
that nothing defines.

**Why not fixed here:** the surrounding code at `functions.rs:2740-2789` is
already mid-investigation for the *exact same class* of bug (a `.to_text`
cross-unit dispatch gap, dated 2026-09-07, same day as this doc) with an
extensive in-progress comment trail explaining why a naive "just check the
leaf name too" fix is unsafe (`"Imported user methods can share leaves such as
to_text, get, or len; rewriting those qualified calls by leaf alone silently
changes their call target."`). `split_whitespace` is a second, independently
discovered instance of that same open gap; fixing it correctly means fixing
the shared root cause, which the comment trail says is still open. Patching
only this one leaf name would mask the general bug without closing it.

## Recommendation

- (1) and (3) are real compiler defects, not merely undocumented gaps —
  worth tracking as TODOs against the trait cleanup (1) and the
  `functions.rs:2789` cross-unit UFCS dispatch gap (3) respectively.
- (2) needs one confirmation (how `Result[Unit, E]` resolves its `Unit` type
  argument) before a one-line `Unit()` -> `()` fix can be applied safely.
- None of the three block the primary fix in this change (the two
  `rt_file_*_create_excl_no_follow` Rust-runtime twins); they are independent,
  pre-existing Stage 2 link failures uncovered only because those two runtime
  symbols were fixed first.
