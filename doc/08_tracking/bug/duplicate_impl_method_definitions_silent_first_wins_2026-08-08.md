# Duplicate `impl` method definitions across files — silent, no dedup, no error

Filed 2026-08-08. Follow-up to an Opus review of the `lower_tuple_lit` fix
(`ec9ff78876c`, see
`native_pushed_tuple_into_empty_literal_list_unboxed_2026-08-02.md`), which
noticed `lower_tuple_lit` is defined TWICE inside `impl MirLowering:` — once
in `src/compiler/50.mir/_MirLoweringExpr/literals.spl:562` and once in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3683`. Both
copies were patched identically by the same commit, so today's behaviour is
consistent, but two live definitions of one method name is itself a defect
class: a future fix applied to only one copy would silently diverge, which is
exactly the failure mode that made the underlying tuple bug recur three
times.

## 1. Which `lower_tuple_lit` actually executes — marker evidence

Added an unconditional `eprint("MARKER_...")` as the very first statement of
each definition (above the docstring), then native-built two independent
programs that lower tuple literals:

- Driver A: `test/fixtures/native_tuple_to_text/main.spl` via
  `scripts/check/check-native-tuple-to-text.shs`'s own `native-build`
  invocation (3 tuple literals in the fixture).
- Driver B: a fresh minimal fixture (`val t = (7, "hi", false)`) built from
  scratch with its own `--source`/`--cache-dir`, independent of Driver A's
  cache.

Results (grepping the captured `native-build` stdout+stderr log):

| Driver | `literals.spl` marker fires | `method_calls_literals.spl` marker fires |
|---|---|---|
| A (3 tuple lits) | 0 | 3 |
| B (1 tuple lit)  | 0 | 1 |

`method_calls_literals.spl:3683`'s `lower_tuple_lit` is the one that runs
under `native-build`, every time, in both independent drivers. The copy at
`literals.spl:562` never fired in either driver — it is dead code **under
native-build**. Markers were removed after the probe and removal verified
with `/usr/bin/grep -rn "MARKER_" src/compiler/ | wc -l` → 0.

**Scope of this proof, stated explicitly:** both drivers went through
`native-build` only. This repo has three independently-diverging execution
engines (interpreter, JIT, native/AOT — see
`reference_neither_engine_trustworthy_2026-07-27.md` and siblings), and a
method proven dead under one engine is not proven dead under the others.
**No deletion was made** on the strength of this evidence alone — see §5.

## 2. Resolution semantics — how two same-named `impl` methods coexist

Located via the Rust bootstrap interpreter (the engine that executes these
`.spl` files, since the self-hosted binary bootstraps from it):

- **Registration** (`src/compiler_rust/compiler/src/interpreter_eval.rs:972-975`):
  `impl_methods` is `HashMap<String, Vec<Arc<FunctionDef>>>`, keyed by type
  name. Each `impl MirLowering:` block encountered while evaluating a module
  **appends** its methods to the `Vec` for `"MirLowering"`:
  ```rust
  let methods = impl_methods.entry(type_name.clone()).or_default();
  for method in &impl_block.methods {
      methods.push(Arc::new(tagged_method(method)));
  }
  ```
  No overwrite, no duplicate-name check. `trait_coherence.rs`'s
  overlap/coherence checks are scoped to *trait* impls only, so plain
  inherent `impl` blocks (this case) are never checked. A mirrored path in
  `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs:271-348`
  does the same append into `GLOBAL_IMPL_METHODS` / `classes[...].methods`.
- **Resolution** (call sites, e.g.
  `src/compiler_rust/compiler/src/interpreter_method/mod.rs:279`,
  `interpreter_helpers/method_dispatch.rs:678,703,767`,
  `interpreter_call/mod.rs:1150`, `interpreter/expr/calls.rs:502,653,658`,
  `interpreter/expr/ops.rs:161,166,199,204`): every one resolves via
  `methods.iter().find(|m| m.name == method)` — Rust's `Iterator::find`
  returns the first matching element, so whichever definition was **pushed
  first** (i.e. whichever file/impl-block the module loader processed
  first) is the one that answers every call; the later duplicate sits inert
  in the `Vec` forever.

**Open discrepancy, stated honestly rather than resolved by guessing:** file
name order would put `literals.spl` before `method_calls_literals.spl`
alphabetically, which under a naive "first-wins by sorted file order" model
predicts `literals.spl` should win — but the marker evidence in §1 shows the
opposite. Module/file load order is therefore governed by something other
than lexical filename sort (likely declaration order in a manifest, import
graph order, or directory-scan order) — this was not tracked down further;
it doesn't change the "first-registered-wins, no error" verdict, only which
concrete file counts as "first" for a given build.

**Generalisable finding:** the language has **no duplicate-inherent-method
detection at all**. Any two `impl SameType:` blocks anywhere in the source
tree that both define a method of the same name will silently coexist, with
whichever is registered first winning every call, and zero diagnostic.

## 3. Repo-wide enumeration

Extracted every `    me name(...)` under an `impl Type:` header across
`src/compiler/**/*.spl` (indentation-anchored regex scan; **not a complete
enumeration** — a sanity check via `/usr/bin/grep -rc "^    me " --include='*.spl'`
counted 2768 total method lines against the scan's 1771, so nested impls,
multi-line/generic `impl Type<T>:` headers, and non-4-space-indent bodies are
undercounted here and would need a proper AST-based pass to close the gap).

Within what was captured, **51 distinct `impl_type|method_name` keys are
defined in more than one file**. Sampled 10 across different impl types and
compared full signatures line-for-line — **all 10 were identical-signature
true duplicates**, not overloads (this codebase does support same-class
overloading, so signature comparison matters; one same-*file* duplicate,
`BasicBlock.record_use` in
`src/compiler/55.borrow/borrow_check/nll.spl:163,445`, *is* a legitimate
overload — different parameter lists — and is excluded from the defect
count).

Confirmed twin-file pairs (all with identical signatures on the sampled
methods):

| impl type | file A | file B | sample dup methods |
|---|---|---|---|
| `MirLowering` | `50.mir/_MirLoweringExpr/literals.spl` | `50.mir/_MirLoweringExpr/method_calls_literals.spl` | 13 methods — **literals.spl is 100% subsumed**: every one of its 13 methods also exists in method_calls_literals.spl (39 methods total) |
| `MirToC` | `70.backend/backend/_CBackendTranslate/class_core.spl` | `70.backend/backend/c_backend_translate_ops.spl` | `translate_binop`, `translate_operand`, `translate_unaryop`, `translate_intrinsic`, `translate_container_call`, `translate_const_value`, `translate_composite_const`, `prepare_stack_slots`, `get_operand_type`, `get_local_type_from_body`, `ensure_stack_slot`, `emit_pointer_assign`, `emit_bulk_copy`, `const_to_i64_expr` |
| `MirInterpreter` | `95.interp/mir_interp_ops.spl` | `95.interp/mir_interpreter.spl` | `execute_binop`, `execute_unaryop`, `execute_const`, `_execute_intrinsic`, `_call_function`, `_pop_call_stack` |
| `ScopeTracker` | `30.types/higher_rank_poly_phase5b.spl` | `30.types/higher_rank_poly_types.spl` | `enter_scope`, `exit_scope` |
| `QuantifierContext` | `30.types/higher_rank_poly_phase5b.spl` | `30.types/higher_rank_poly_types.spl` | `reset`, `fresh_skolem`, `enter_forall`, `exit_forall`, `bind_var` |
| `VarianceEnv` | `30.types/variance_phase6a.spl` | `30.types/variance_types.spl` | `set_type_variance`, `set_type_variances` |
| `MacroRegistry` | `10.frontend/parser/macro_registry.spl` | `30.types/macro_def.spl` | `register_macro` |
| `TreeSitter` | `10.frontend/treesitter/outline.spl` | `10.frontend/treesitter.spl` | `parse_outline` |
| `ObjectProvider` | `70.backend/linker/object_provider.spl` | `99.loader/loader/object_provider.spl` | `add_library` — **both files also independently declare `struct ObjectProvider` and `struct ObjectProviderConfig`**, so this may be two genuinely separate types that happen to share a name across unrelated backend subsystems (linker vs. loader) rather than one accidentally-split impl; not resolved further here |
| `IncrementalState` | `80.driver/incremental_builder.spl` | `80.driver/incremental.spl` | `mark_dirty` — both files independently declare `class IncrementalState`, same caveat as above |
| `AssocTypeProjection` | `25.traits/associated_types.spl` | `30.types/associated_types_solvers.spl` | `set_resolved` |
| `ProceedContext` | `90.tools/aop_proceed_minimal.spl` | `90.tools/aop_proceed.spl` | `mark_proceed_called` |

The `ObjectProvider`/`IncrementalState` rows carry a caveat the others don't:
both sides declare their *own* `struct`/`class` of that name, so these might
be two unrelated types with a coincidental name collision (each file's `impl`
binds to its own local type) rather than one type split across two files.
This needs an AST/type-identity check (is it the same `TypeId`, or two
distinct types that happen to print the same name?) to settle — flagged, not
resolved.

## 4. `compiler_infer_types` / `compiler_instantiate_template` — different phenomenon, NOT the impl-duplicate class

Two prior symbol-collision sweeps skipped these as "a probable duplicate-FILE
bug rather than a naming collision." Investigated: **it is a duplicate FILE,
but a deliberate one, not the same accidental-impl-split phenomenon as
`lower_tuple_lit`.**

- `src/compiler/99.loader/compiler_sffi.spl` (82 lines) opens with the
  comment `# Compatibility compiler_sffi surface for interpreter/test
  runner.` and defines `compiler_infer_types`/`compiler_instantiate_template`
  as literal no-op stubs (`"{}"` returned unconditionally, `[]`/`""`/`false`
  for the other 18 functions in the file).
- `src/compiler/99.loader/loader/compiler_sffi.spl` (914 lines, 44 functions)
  is the real implementation.
- These are free top-level `fn`, not `impl` methods, so they are **not**
  subject to the `Vec`+`find` inherent-method resolution in §2 at all — they
  are resolved by normal module-import scoping (`use compiler.loader.X`
  picks a specific module path).
- Call-site check: `src/compiler/70.backend/linker/obj_taker.spl:19` imports
  `compiler.loader.loader.compiler_sffi.*` — the **real** implementation.
  But `src/compiler/99.loader/loader/jit_instantiator.spl:16` — itself living
  right next to the real implementation — imports
  `compiler.loader.compiler_sffi.{...}`, i.e. the **stub** file one directory
  up. If `jit_instantiator.spl` relies on `compiler_instantiate_template`
  doing real work, it is silently getting `"{}"` back. **Not chased further
  here** — flagging as a possible separate, real defect worth its own bug
  doc/probe, distinct from the duplicate-impl-method class this doc is
  about.

**Verdict: not the same phenomenon.** The prior sweeps' instinct
("duplicate-FILE bug") was directionally right but the mechanism is
different: a documented compatibility/stub module coexisting with the real
module at a sibling path, disambiguated by which module each caller
explicitly imports — not an accidental split of one `impl` block's methods
across files with no dedup. The renaming those sweeps declined to do would
not have been safe either way, for a different reason: renaming risks
breaking whichever callers intentionally use the stub as a stub.

## 5. Disposition — no deletion

Per the proof bar in this investigation's brief ("provably dead… across more
than one driver"), `literals.spl:562`'s `lower_tuple_lit` has two-driver
proof of deadness, but only within a single engine (`native-build`). Given
this repo's well-documented engine divergence (interpreter/JIT/native each
behave differently on unrelated bugs — see
`reference_neither_engine_trustworthy_2026-07-27.md`), and given that
`literals.spl` is 100% subsumed (all 13 of its methods duplicate into
`method_calls_literals.spl`, not just this one), the correct fix is "delete
the whole now-vestigial `literals.spl` file" — not "delete one method from
it" — and that requires interpreter- and JIT-engine confirmation this doc did
not gather. **No code was deleted or otherwise changed by this
investigation; markers were added and fully removed.**

## Recommended follow-ups (not done here)
1. Confirm `literals.spl` is dead under the interpreter and JIT engines too
   (not just native-build), then delete the whole file in one change (all 13
   methods, not a partial cleanup).
2. Add a duplicate-inherent-method diagnostic at `impl` registration time
   (`interpreter_eval.rs:972-975` / the mirrored
   `evaluation_helpers.rs:271-348` path) — at minimum a warning when a
   `Vec` for a type name already contains a method of the same name being
   pushed.
3. Work through the other 11 twin-file pairs in §3 the same way: determine
   whether each is an accidental split (dead-code risk, same defect class)
   or, like `ObjectProvider`/`IncrementalState`, a coincidental same-name
   type in unrelated modules (not a defect).
4. Follow up on `jit_instantiator.spl` importing the `compiler_sffi.spl`
   *stub* instead of the real `loader/compiler_sffi.spl` implementation
   (§4) — separate bug, not filed yet.
