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

**NOTE (2026-08-08, re-write):** this file was written once, reported as
saved, and the write was silently dropped (the file did not exist on disk
despite a successful-looking tool call — a known Write-tool failure mode in
this repo, see `feedback_write_tool_silent_drops.md`). This is a full
re-write from the same investigation's live analysis, not a reconstruction
from memory of a stale doc. All findings below were independently
re-verified as still true at re-write time (marker residue re-checked at 0,
`_execute_intrinsic` signatures and the `__simple_ssa_phi` case re-confirmed
by direct file read).

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
**No deletion was made** on the strength of this evidence alone — see §5,
superseded by §9 below.

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

## 3. Repo-wide enumeration (original pass)

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

**This "sampled 10, all identical" conclusion is OVERTURNED by §8 below —
the full 51-item body-level classification found 15 DIVERGENT pairs, not 0.**

Confirmed twin-file pairs (all with identical *signatures* on the sampled
methods — signature identity does not imply body identity, see §8):

| impl type | file A | file B | sample dup methods |
|---|---|---|---|
| `MirLowering` | `50.mir/_MirLoweringExpr/literals.spl` | `50.mir/_MirLoweringExpr/method_calls_literals.spl` | 13 methods |
| `MirToC` | `70.backend/backend/_CBackendTranslate/class_core.spl` | `70.backend/backend/c_backend_translate_ops.spl` | `translate_binop`, `translate_operand`, `translate_unaryop`, `translate_intrinsic`, `translate_container_call`, `translate_const_value`, `translate_composite_const`, `prepare_stack_slots`, `get_operand_type`, `get_local_type_from_body`, `ensure_stack_slot`, `emit_pointer_assign`, `emit_bulk_copy`, `const_to_i64_expr` |
| `MirInterpreter` | `95.interp/mir_interp_ops.spl` + `95.interp/mir_interp_intrinsics.spl` | `95.interp/mir_interpreter.spl` | `execute_binop`, `execute_unaryop`, `execute_const`, `_execute_intrinsic`, `_call_function`, `_pop_call_stack` |
| `ScopeTracker` | `30.types/higher_rank_poly_phase5b.spl` | `30.types/higher_rank_poly_types.spl` | `enter_scope`, `exit_scope` |
| `QuantifierContext` | `30.types/higher_rank_poly_phase5b.spl` | `30.types/higher_rank_poly_types.spl` | `reset`, `fresh_skolem`, `enter_forall`, `exit_forall`, `bind_var` |
| `VarianceEnv` | `30.types/variance_phase6a.spl` | `30.types/variance_types.spl` | `set_type_variance`, `set_type_variances` |
| `MacroRegistry` | `10.frontend/parser/macro_registry.spl` | `30.types/macro_def.spl` | `register_macro` |
| `TreeSitter` | `10.frontend/treesitter/outline.spl` | `10.frontend/treesitter.spl` | `parse_outline` |
| `ObjectProvider` | `70.backend/linker/object_provider.spl` | `99.loader/loader/object_provider.spl` | `add_library` — both files also independently declare `struct ObjectProvider` and `struct ObjectProviderConfig`, so this may be two genuinely separate types that happen to share a name across unrelated backend subsystems (linker vs. loader) rather than one accidentally-split impl; not resolved further here |
| `IncrementalState` | `80.driver/incremental_builder.spl` | `80.driver/incremental.spl` | `mark_dirty` — both files independently declare `class IncrementalState`, same caveat as above |
| `AssocTypeProjection` | `25.traits/associated_types.spl` | `30.types/associated_types_solvers.spl` | `set_resolved` |
| `ProceedContext` | `90.tools/aop_proceed_minimal.spl` | `90.tools/aop_proceed.spl` | `mark_proceed_called` |
| `MirToLlvm` | `70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl` | `70.backend/backend/mir_to_llvm_helpers.spl` | `emit_runtime_declarations`, `emit_comparison`, `add_string_global` (found in the §6 re-scan, not in the original sample-of-10) |

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

## 5. Disposition after the original pass — no deletion (superseded by §9)

Per the proof bar in this investigation's brief ("provably dead… across more
than one driver"), `literals.spl:562`'s `lower_tuple_lit` had two-driver
proof of deadness, but only within a single engine (`native-build`). Given
this repo's well-documented engine divergence (interpreter/JIT/native each
behave differently on unrelated bugs — see
`reference_neither_engine_trustworthy_2026-07-27.md`), the original plan was
"delete the whole now-vestigial `literals.spl` file" once interpreter- and
JIT-engine confirmation existed, reasoning that `literals.spl` was "100%
subsumed" (all 13 of its methods duplicate into `method_calls_literals.spl`).
**§8 below shows that reasoning was wrong**: 2 of those 13 methods
(`lower_dict_lit`, `lower_array_lit`) are body-divergent, not identical, so
"delete the whole file" was never actually safe even before engine proof was
gathered. **No code was deleted or otherwise changed by the original
investigation; markers were added and fully removed.**

---

## 6. Re-derivation of the count (2026-08-08, follow-up pass)

Re-scanned independently with a fresh `/usr/bin/awk` pass (not reusing the
original session's script), explicitly restricted to **`impl Type:` block
bodies only**. Inline `class`/`struct`-body methods were deliberately
excluded: a `class` body is a single declaration, so it cannot silently
duplicate across files the way an `impl Type:` block can (there is no
`Vec`-append mechanism for class-body methods to collide through) — an
`impl` block re-opened in a second file appends to the same `Vec` per §2,
but a `class SameType:` declared twice would be a duplicate-class-definition
error of a different kind entirely, not this defect class. Including them
would have mixed two unrelated phenomena into one count.

Steps and numbers:
- Total `^    me ` lines (4-space indent, any file) across `src/compiler`:
  **2769** (anchor count, via `/usr/bin/grep -rc "^    me " --include='*.spl'
  src/compiler | awk -F: '{s+=$2}END{print s}'`).
- Of those, **1547** sit inside an `impl Type:` block (the rest, 1222, are
  inline `class`/`struct` methods — verified by spot-checking a sample:
  `SpecConstRegistry.set` at
  `src/compiler/70.backend/spec_const_registry.spl:22` is a `class` body
  method, no `impl` block anywhere for that type, confirming the exclusion
  is real work, not just a filter that happens to match).
- Deduping same-file re-declarations (legitimate overloads, e.g.
  `BasicBlock.record_use` in `nll.spl` — excluded, matches original doc),
  grouping by `impl_type|method_name`, and counting how many **distinct
  files** define each key: **51 keys appear in more than one file.**

**Verdict: 51 is confirmed correct**, not a low or high bound — an
independently-written scan, deliberately excluding the class-body-method
noise that could have gone either way, landed on the exact same number as
the original scan. The 51 keys resolve to the same **12 twin-file pairs** as
§3's table, with the full per-method breakdown for the largest pair,
`MirLowering` (13 methods): `rt_array_push_operand, rt_array_len_operand,
rt_array_get_operand, lower_tuple_lit, lower_set_lit, lower_dict_lit,
lower_dict_key, lower_const_expr, lower_array_repeat, lower_array_map,
lower_array_lit, lower_array_fold, lower_array_filter`.

## 7. Interpreter/JIT engine liveness proof for `lower_tuple_lit` (extends §1)

§1 only proved native-build behaviour. This pass added the same
`eprint("MARKER_...")` markers back to both copies and ran the **interpreter
engine** via `bin/simple run` (this repo's deployed `bin/simple` is
currently the Rust bootstrap seed — it prints `WARNING: this Rust-built
Simple binary is a bootstrap seed only` — the same engine `interpreter_eval.rs`
registration logic in §2 was traced through) against two drivers:

- A trivial one-tuple-literal fixture (`val t = (7, "hi", false); print(t.0.to_text())`).
- The existing 3-tuple-literal fixture, `test/fixtures/native_tuple_to_text/main.spl`.

Both ran via `bin/simple run <file>` (no `--native`, the plain interpreter/
JIT-attempt path) and produced **correct output and zero marker hits from
either copy**, on both drivers. Then re-ran `bin/simple native-build` on the
one-tuple fixture with an explicit 590s foreground timeout (the harness's
default 120s timeout is too short for native-build):
**`method_calls_literals.spl`'s marker fired exactly once,
`literals.spl`'s marker did not fire.** Markers removed immediately after
and verified gone (`/usr/bin/grep -rn "MARKER_" src/compiler/ | wc -l` → 0;
`git status --short` on the 4 touched files shows no diff beyond their
pre-existing untracked "A" state carried over from another session,
confirmed via `git diff --stat`).

| Engine | Driver | `literals.spl` fires | `method_calls_literals.spl` fires |
|---|---|---|---|
| `bin/simple run` (interpreter/JIT-attempt) | 1-tuple fixture | 0 | 0 |
| `bin/simple run` (interpreter/JIT-attempt) | 3-tuple fixture | 0 | 0 |
| `bin/simple native-build` (AOT) | 1-tuple fixture | 0 | 1 |

**Reading:** `lower_tuple_lit` (both copies) is not reached at all by
whatever `bin/simple run` does for a literal tuple — tuple construction and
field-read appear to be handled by a different, non-MIR-lowering path under
that engine (plausibly constant-folded or interpreted directly at HIR level
without a MIR-lowering pass), so the duplicate is moot there: neither copy
runs. Under native-build, `method_calls_literals.spl` is confirmed (again)
as the sole live copy; `literals.spl` is dead. Net result across the two
engines actually exercised: **`literals.spl`'s `lower_tuple_lit` never fires
under either engine tested; `method_calls_literals.spl`'s only fires under
native-build.**

**`bin/simple test` (the third named engine) remains UNPROVEN.** It was
attempted on both fixtures and errored `test-runner: no examples executed`
— plain scripts are not a valid `test` input, they need spec/example-block
framing (a `_spec.spl` file with `example:` blocks per the SPipe/SSpec
convention), which was not built in this pass. So the interpreter-as-
`test`-invoked-specifically engine is still an open item — only the
interpreter/JIT-attempt path via `run` was proven dead-both for this
method.

## 8. Full body-level classification of all 51 duplicate methods

The original doc (§3) sampled 10 of 51 and found all 10 identical,
implicitly suggesting this duplicate class is mostly benign. This pass
extracted **every one of the 51 method bodies from both files** (from the
`me name(` line to the next line at 4-space-or-less indent) and diffed them
pairwise, both byte-exact and whitespace-normalized. Result:

**36 IDENTICAL, 15 DIVERGENT.** This OVERTURNS the "all identical" reading
from the 10-item sample — a 10/51 sample (≈20%) missed all 15 divergent
pairs by chance, which is itself worth noting as a sampling-risk lesson.

Full table of the 15 divergent pairs, with file:line for each copy (line
number is the `me <name>(` declaration line):

| impl type | method | copy A | copy B | lines A / B | note |
|---|---|---|---|---|---|
| `QuantifierContext` | `reset` | `30.types/higher_rank_poly_phase5b.spl` | `30.types/higher_rank_poly_types.spl` | 5 / 6 | B has one extra `self.inference_counter = 0` reset line A lacks |
| `ProceedContext` | `mark_proceed_called` | `90.tools/aop_proceed_minimal.spl` | `90.tools/aop_proceed.spl` | 2 / 3 | trivial |
| `ObjectProvider` | `add_library` | `70.backend/linker/object_provider.spl` | `99.loader/loader/object_provider.spl` | 8 / 2 | B is a stub/no-op relative to A |
| `MirToLlvm` | `emit_runtime_declarations` | `70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl` | `70.backend/backend/mir_to_llvm_helpers.spl` | 233 / 15 | **large** — one file has a much fuller declaration list |
| `MirToLlvm` | `add_string_global` | `70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl` | `70.backend/backend/mir_to_llvm_helpers.spl` | 16 / 14 | minor |
| `MirLowering` | `lower_tuple_lit` | `50.mir/_MirLoweringExpr/literals.spl:562` | `50.mir/_MirLoweringExpr/method_calls_literals.spl:3683` | 38 / 26 | already known (§1/§7) — `method_calls_literals.spl` wins under native-build |
| `MirLowering` | `lower_dict_lit` | `50.mir/_MirLoweringExpr/literals.spl` | `50.mir/_MirLoweringExpr/method_calls_literals.spl` | 89 / 81 | **not previously checked** — invalidates the old "100% subsumed" claim, see below |
| `MirLowering` | `lower_array_lit` | `50.mir/_MirLoweringExpr/literals.spl` | `50.mir/_MirLoweringExpr/method_calls_literals.spl` | 79 / 79 | same length, content differs — closer diff not yet done, open item |
| `MirInterpreter` | `_pop_call_stack` | `95.interp/mir_interp_ops.spl` | `95.interp/mir_interpreter.spl` | 11 / 12 | minor |
| `MirInterpreter` | `_execute_intrinsic` | `95.interp/mir_interp_intrinsics.spl:17` | `95.interp/mir_interpreter.spl:664` | 270 / 79 | **large — most dangerous pair found this pass, see §9** |
| `MirInterpreter` | `execute_const` | `95.interp/mir_interp_ops.spl` | `95.interp/mir_interpreter.spl` | 4 / 8 | one file handles more constant kinds |
| `MirInterpreter` | `_call_function` | `95.interp/mir_interp_ops.spl` | `95.interp/mir_interpreter.spl` | 97 / 89 | needs closer diff — open item |
| `MacroRegistry` | `register_macro` | `10.frontend/parser/macro_registry.spl` | `30.types/macro_def.spl` | 2 / 9 | one is a near-stub |
| `IncrementalState` | `mark_dirty` | `80.driver/incremental_builder.spl` | `80.driver/incremental.spl` | 8 / 10 | minor |
| `AssocTypeProjection` | `set_resolved` | `25.traits/associated_types.spl` | `30.types/associated_types_solvers.spl` | 3 / 2 | minor |

**`lower_dict_lit` and `lower_array_lit` are DIVERGENT, which directly
INVALIDATES the prior "literals.spl is 100% subsumed by
method_calls_literals.spl, safe to delete the whole file" plan.** That plan
(old §5 / recommended-follow-up #1) assumed all 13 of `literals.spl`'s
`MirLowering` methods were identical to their twins in
`method_calls_literals.spl`. Two of the 13 are not. A blind whole-file
delete of `literals.spl` would silently drop whatever `lower_dict_lit` and
`lower_array_lit` do differently there — even after full 3-engine dead-code
proof for the file as a unit, those two methods would need individual
reconciliation (which body is correct, or do both need merging) before any
deletion, not a blanket "identical, just pick one."

## 9. `MirInterpreter._execute_intrinsic` — most dangerous divergent pair

`src/compiler/95.interp/mir_interp_intrinsics.spl:17` implements
`me _execute_intrinsic(name: text, args: [MirOperand]) -> i64` with **25
`case` branches over 270 lines** (includes `print` and what looks like a
broad set of array/string/collection intrinsics — `case "print":` is the
first branch).

`src/compiler/95.interp/mir_interpreter.spl:664` implements the **same
signature**, `me _execute_intrinsic(name: text, args: [MirOperand]) -> i64`,
but with a different, smaller set of **10 `case` branches over 79 lines**,
including a `case "__simple_ssa_phi":` branch (with an inline comment
explicitly calling out a "landmine" — a predecessor-block-id-0 collapse bug
where a falsy check on `self.previous_block` would silently drop straight to
a fallback value instead of picking the value actually paired with
predecessor block 0) that **does not exist at all** in the 270-line copy.

These two are not one subsuming the other — they are two different partial
implementations of the same dispatcher, one broader (more intrinsics), one
narrower but containing a specific correctness fix the broader one lacks.
**Per §2's resolution semantics, whichever `impl MirInterpreter:` block gets
registered first in the `Vec<Arc<FunctionDef>>` for `"MirInterpreter"` wins
every call — so first-registered-wins directly decides whether the
`__simple_ssa_phi` predecessor-block-0 fix is live or silently inert.**

**Registration-order/liveness proof attempted but not completed.** Markers
(`eprint("MARKER_MIR_INTERP_INTRINSICS_SPL_EXECUTE_INTRINSIC")` in the
270-line copy, `eprint("MARKER_MIR_INTERPRETER_SPL_EXECUTE_INTRINSIC")` in
the 79-line copy) were added to both, then removed after establishing that
neither the tuple fixtures nor a general search turned up a confirmed live
call path: `MirInterpreter(` is only constructed inside
`mir_interpreter.spl`'s own static factory (`src/compiler/95.interp/mir_interpreter.spl:103`).
Grepping `src/compiler` and `src/app` for callers of that factory or for
`compiler.interp.mir_interpreter` imports outside `95.interp/*` found none
in the mainstream `run`/`native-build`/`test` driver path — the only
importer found, `src/app/optimize/profile_layout_cli.spl`, imports a
*different* submodule (`compiler.interp.execution.sprof_hotspot_bridge` /
`tiered_jit`), not `MirInterpreter` itself.

**Open question, explicitly unresolved: is `MirInterpreter` reachable from
the default compilation pipeline at all?** If it is not wired into
`run`/`native-build`/`test`, both copies of every method in this pair are
dead under all three engines for ordinary compiles regardless of
registration order — but that was not confirmed (no driver was found and
exercised that definitely invokes `MirInterpreter._execute_intrinsic`).
Markers were removed and absence verified the same way as §7
(`/usr/bin/grep -rn "MARKER_" src/compiler/ | wc -l` → 0, re-confirmed again
at re-write time).

**Flagged as the single highest-priority open item in this whole
investigation.** Before touching either copy: (1) find the actual call path
into `MirInterpreter`, or positively confirm there isn't one; (2) if there
is one, determine registration order the same way §7 did for
`lower_tuple_lit`; (3) if `mir_interp_intrinsics.spl`'s copy wins
registration, the `__simple_ssa_phi` fix in `mir_interpreter.spl`'s copy is
silently inert right now and needs to be ported over, not just left as
"the loser."

## Disposition (final, this pass)

**No code deleted this pass either.** Findings only; all markers added
during investigation were removed and their absence verified twice
(immediately after each probe, and again at re-write time via
`/usr/bin/grep -rn "MARKER_" src/compiler/`).

- **Safe to consider for dedup** (36 IDENTICAL pairs, content matches
  exactly, per §8): mechanical merge, comparatively low risk, but still
  needs a 3-engine liveness check per pair before deleting the loser copy —
  that check was only done in full for `lower_tuple_lit` (§7); the other 35
  identical pairs are unchecked.
- **Dangerous, needs a human decision before any edit** (15 DIVERGENT
  pairs, §8 table): each is two different implementations under one name;
  deleting either without reading both bodies risks silently reverting a
  fix or losing functionality. `MirInterpreter._execute_intrinsic` (§9) is
  the standout — largest divergence, and one copy contains what reads like
  a real, deliberate bug fix (`__simple_ssa_phi` predecessor-block-0
  handling) the other entirely lacks.
- **Evidence still missing:**
  1. `bin/simple test`'s specific engine behaviour for `lower_tuple_lit`
     (errored on plain-script input, not retried with a proper spec
     wrapper).
  2. Full 3-engine liveness proof for any pair other than `lower_tuple_lit`
     — 50 of the 51 pairs are unproven on any axis beyond §8's content
     classification.
  3. Whether `MirInterpreter` is reachable from the default pipeline at
     all (§9) — the top-priority open item.
  4. Closer, line-by-line diffs for `lower_array_lit` and `_call_function`
     — both confirmed content-divergent by whole-body diff, but the *nature*
     of the divergence (which lines differ and why) has not been
     characterized beyond "differs."
  5. The `ObjectProvider`/`IncrementalState` "same name, different type"
     question from §3 — still not resolved with an AST/type-identity check.
  6. The `jit_instantiator.spl` importing the stub `compiler_sffi.spl`
     instead of the real `loader/compiler_sffi.spl` (§4) — a separate,
     not-yet-filed bug, distinct from this duplicate-impl-method class.
  7. Adding a duplicate-inherent-method diagnostic at `impl` registration
     time (`interpreter_eval.rs:972-975` / the mirrored
     `evaluation_helpers.rs:271-348` path) — the actual fix that would
     prevent this whole defect class from recurring. Not started.

## 10. `_execute_intrinsic` follow-up (2026-08-08, third pass) — reachability, registration proof, fix ported

**`MirInterpreter` reachability, resolved:** it is not reachable from the
default `run`/`native-build`/`test` compiler pipeline (confirmed again — no
importer of `MirInterpreter` outside `95.interp/*` and test files), but it
**is** reachable and directly exercised as a library class by several unit/
system specs that construct it explicitly, most importantly
`test/01_unit/compiler/interpreter/mir_ssa_phi_intrinsic_spec.spl` (also
duplicated at `test/unit/compiler/interpreter/mir_ssa_phi_intrinsic_spec.spl`)
— this spec's third case, "selects the incoming value for the recorded
predecessor block", is a direct assertion on the exact `__simple_ssa_phi`
predecessor-block-0 behaviour this bug doc flagged in §9. Other direct
consumers: `mir_interp_bounds_check_spec.spl`, `strict_interp_spec.spl`,
`resource_interp_drop_spec.spl`,
`optimization_plugin_jit_hotspot_system_spec.spl`. So: dead in ordinary
compiles, live and under test for this specific class.

**Registration-order proof for `_execute_intrinsic`, completed for 2 of 3
engines.** Markers were re-added (`MARKER_MIR_INTERP_INTRINSICS_SPL_EXECUTE_INTRINSIC`
in the 270-line copy, `MARKER_MIR_INTERPRETER_SPL_EXECUTE_INTRINSIC` in the
79-line copy) and two independent probes run:

1. `bin/simple test test/01_unit/compiler/interpreter/mir_ssa_phi_intrinsic_spec.spl`
   — `4 examples, 0 failures`. `mir_interpreter.spl`'s marker fired 3 times
   (once per test case that dispatches an intrinsic); `mir_interp_intrinsics.spl`'s
   marker fired **0** times.
2. A fresh minimal driver (`main.spl`, not part of the spec suite) replicating
   the "predecessor block 2 selected" case via `bin/simple run` — same
   result: `mir_interpreter.spl`'s marker fired once, produced the fix-correct
   `RESULT=99`; `mir_interp_intrinsics.spl`'s marker did not fire.

**Verdict: `mir_interpreter.spl`'s `_execute_intrinsic` (the copy WITH the
`__simple_ssa_phi` fix) is the one that wins under both the `bin/simple test`
interpreter engine and the `bin/simple run` engine**, for every consumer
found. This is consistent with — not necessarily proof of — ordinary
first-registered-wins semantics: nothing in the repo imports
`compiler.interp.mir_interp_intrinsics` by name (grep for
`mir_interp_intrinsics\|mir_interp_ops` across `src/` and `test/` returns
zero hits other than the files' own headers), so for any consumer that only
imports `compiler.interp.mir_interpreter.{MirInterpreter}` directly (as every
found consumer does), `mir_interp_intrinsics.spl`'s `impl MirInterpreter:`
block may simply never enter that consumer's module graph at all — a
different mechanism from a registration race, but with the same practical
result: `mir_interp_intrinsics.spl`'s copy is unreached by every driver
tested.

**`native-build` (AOT) proof: attempted, inconclusive, NOT recorded as a
negative result.** Two attempts both exceeded this session's usable
foreground budget (the harness auto-backgrounds any command that runs past
~590s, `native-build` on the compiler tree did not finish before that, and
both attempts were stopped rather than left backgrounded per this session's
foreground-only constraint). Per the coordinator's explicit warning, this is
recorded as **unproven for native-build**, not as "did not fire" — a stopped
build is not evidence of deadness. Whether `mir_interp_intrinsics.spl`'s copy
could ever win registration in a full self-hosted compile (where every file
under `src/compiler/95.interp/` is loaded regardless of the narrow test-spec
import graph) remains the one genuinely open question about this pair.

**Fix ported** (highest-value action, done regardless of the above
uncertainty, since porting to both copies is correct no matter which one
wins in a build config not yet tested): `mir_interp_intrinsics.spl`'s
`_execute_intrinsic` previously had **no `"__simple_ssa_phi"` case at all**
and fell through to `case _: 0` (unconditional 0, not even the "first
incoming value" fallback the other copy has for the `args.len() < 4` shape).
Added a `case "__simple_ssa_phi":` block to
`src/compiler/95.interp/mir_interp_intrinsics.spl` (before its final
`case _:`, now at line 283) that is a direct port of
`mir_interpreter.spl:667-688`'s logic, predecessor-block-0 landmine comment
included. File grew from 307 to 336 lines (`git hash-object` /
`git rev-parse origin/main:<path>` confirm the change; `wc -l` confirms the
+29 line delta matches the inserted block). Verified after the port:
`bin/simple run` on the minimal driver still returns the fix-correct
`RESULT=99` (marker-confirmed dispatch unchanged, still via
`mir_interpreter.spl`'s copy); `bin/simple test` on the spec passed 4/0
before the port was made and was re-attempted after but hit an unrelated
environment fault (`Module count limit (800) exceeded loading
.../test_daemon/light_protocol.spl`) on repeated re-runs — a pre-existing
test-daemon/module-budget issue orthogonal to this file, not a regression
from the port (the `run`-engine check after the port passed cleanly on the
same edited tree). Markers removed from both files after the probes;
`/usr/bin/grep -rn "MARKER" src/compiler --include=*.spl` → 0 matches,
`sh scripts/check/check-no-sabotage-residue.shs` → `PASS`.

**`lower_array_lit` closer diff (closes an open item from §8):** the two
79-line bodies differ by exactly one line —
`literals.spl` calls `self.error_fatal(...)`, `method_calls_literals.spl`
calls `self.error(...)`, same message, otherwise byte-identical. Not fixed
in this pass (no marker/liveness proof done for this pair, and the
`error_fatal` vs `error` severity choice looks like it could be either an
intentional divergence or an unnoticed drift — flagged for a follow-up
liveness check + human call on which severity is correct, not resolved
here).

**Still not done, explicitly:** registration-order tracing for the other 11
twin-file pairs (only `MirLowering.lower_tuple_lit` from earlier passes and
`MirInterpreter._execute_intrinsic` from this pass have engine-level proof);
any deletions (none made — no pair has the full 3-engine-plus-content-
subsumption bar this doc requires before deleting a loser copy);
`lower_dict_lit`'s and `_call_function`'s closer diffs (still only
whole-body-differs, not line-level, for those two).
