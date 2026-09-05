# Duplicate `impl` method definitions across files — silent, no dedup, no error

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

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

## 11. Fourth pass (2026-08-08) — remaining 14 divergent pairs classified

Worked the remaining 14 of 15 divergent pairs from §8 (all except
`_execute_intrinsic`, closed in §10). Two techniques replaced per-pair
native-build marker probes (too expensive to run 14 times in one session):

1. **Mechanism-level generalization of registration order** (proven, not
   inferred): §2's Rust snippet shows `impl_methods.entry(type_name)` is
   populated once per **file**, by iterating that file's *whole* `impl
   Type:` block. Confirmed this pass that every twin file in every pair
   checked has **exactly one** `impl Type:` block (`grep -c "^impl Type"`
   per file, all = 1). Consequence: registration order is a property of
   **which file loads first**, not of the individual method — so a
   winner/loser proof for ONE method in a twin-file pair (e.g.
   `lower_tuple_lit` in §7) applies to **every other method in that same
   pair** without re-probing, *provided* both files are actually reachable
   at all (see next point).
2. **Reachability-by-import-graph** (the mechanism §9/§10 already used for
   `MirInterpreter`): for several pairs, one file has **zero importers**
   anywhere in `src/compiler` other than its own header — meaning its
   `impl` block is never loaded into any real compiler run, so the
   "registration race" never happens; the other file's copy is simply the
   only one that exists at runtime. This is a stronger, static claim than a
   dynamic marker probe and was cross-checked against `grep -rln
   "<module-path>" src/compiler` for each candidate orphan.

### Classification table (14 pairs, `_execute_intrinsic` excluded — done in §10)

| impl type | method | copy A | copy B | class | verdict / winner |
|---|---|---|---|---|---|
| `QuantifierContext` | `reset` | `higher_rank_poly_phase5b.spl` | `higher_rank_poly_types.spl` | **winner-is-fine** | A (`phase5b.spl`) has **zero importers** anywhere in `src/compiler` (only a stale mention in `PHASE_FILES.md`) — orphan file, never loaded. B is the sole live copy and already has the extra `self.inference_counter = 0` reset A lacks. |
| `ScopeTracker` | `enter_scope`/`exit_scope` | same pair | same pair | **winner-is-fine** (by extension) | Same orphan-file reasoning as `reset` — not independently body-diffed this pass (sampled originally as identical), but per §8 these two methods were not in the divergent list; included here only to note the same reachability finding applies to the whole `phase5b.spl` file, not just `reset`. |
| `ProceedContext` | `mark_proceed_called` | `aop_proceed_minimal.spl` | `aop_proceed.spl` | **cosmetic** | Diff is a docstring-only addition (`"""Record that proceed() was called."""`); behavior identical. Demote to the identical bucket. |
| `ObjectProvider` | `add_library` | `linker/object_provider.spl` | `loader/object_provider.spl` | **dangerous, unresolved** | Both declare their own `class ObjectProvider` (name-collision caveat from §3) — but this pass found they are **cross-imported into the same process**: `linker/object_provider_adapter.spl` imports `compiler.loader.object_provider.{ObjectProvider,...}` (the loader's class) while `loader/module_loader.spl` imports `compiler.backend.linker.object_provider.{ObjectProvider,...}` (the linker's class). Since `impl_methods` is keyed by the bare string `"ObjectProvider"`, both `impl` blocks genuinely can collide in one interpreter session, not just "coincidentally same name." Bodies differ substantially: linker's copy (8 lines) checks `result.is_ok()` and dedups into `self.config.libraries`; loader's copy (2 lines) is a bare `self.getter.add_library(lib_path)` passthrough with no error handling or config tracking. **Registration-order winner NOT traced this pass** (time-boxed out) — flagged as the top remaining open item alongside `_call_function` below. |
| `MirToLlvm` | `emit_runtime_declarations` | `_MirToLlvm/asm_constraints_helpers.spl` | `mir_to_llvm_helpers.spl` | **winner-is-fine** | `mir_to_llvm.spl` (the only module that constructs `MirToLlvm`) explicitly imports `_MirToLlvm.asm_constraints_helpers.*`; `mir_to_llvm_helpers.spl` has **zero importers** anywhere in `src/compiler` — confirmed orphan. Independently corroborated by an existing code comment at `src/compiler/80.driver/driver_bootstrap.spl:282-283` (`bootstrap_is_runtime_declared_name`'s docstring) stating "Names `emit_runtime_declarations()` (`asm_constraints_helpers.spl`) always statically pre-declares..." — written by an earlier engineer who observed exactly this at build time. The orphan copy's body isn't even a subsumption/superset of the winner's — it's unrelated matrix/broadcast-op stub declarations, a different abandoned feature attempt. |
| `MirToLlvm` | `add_string_global` | same pair | same pair | **winner-is-fine** | Same reachability as above. Winner has an extra `SIMPLE_BOOTSTRAP=1`-gated branch (`llvm_bootstrap_string_globals_add`) the orphan lacks. |
| `MirLowering` | `lower_tuple_lit` | `literals.spl` | `method_calls_literals.spl` | **winner-is-fine** (already proven, §7) | `method_calls_literals.spl` wins under native-build (both dead under interpreter/JIT — tuple construction never reaches MIR lowering there). |
| `MirLowering` | `lower_dict_lit` | `literals.spl` | `method_calls_literals.spl` | **needs follow-up** | Same twin pair as `lower_tuple_lit`/`lower_array_lit`, so by the mechanism proof above `method_calls_literals.spl` wins here too — but the 89-vs-81-line body divergence was not diffed line-by-line this pass (still an open item carried from §8). |
| `MirLowering` | `lower_array_lit` | `literals.spl` | `method_calls_literals.spl` | **RESOLVED — real correctness gap, already being fixed** | Full line-by-line diff (this pass): the two 79/80-line bodies differ by **exactly one line** — `literals.spl` (loser, dead under native-build per the same-pair proof) calls `self.error_fatal(...)`; `method_calls_literals.spl` (winner) called `self.error(...)`. Read `error()`/`error_fatal()`'s own docstrings at `src/compiler/50.mir/_MirLowering/asm_and_targets.spl:264-286`: `error_fatal`'s docstring explicitly says "Use this at every site that continues past the error and emits a placeholder operand (a const 0/3...)" — which is **exactly** what this call site does (`operands.push(MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(0), ...)))` right after the error call). So the winning copy was using the deprecated non-fatal path at a site its own sibling function's docstring identifies as a must-be-fatal pattern: an array literal with an unlowerable element (e.g. certain lambda-literal elements) silently continued with a placeholder `0` instead of aborting the build — same family as the tuple-OOB `error`-vs-`error_fatal` defect from `21e3950b7da` the task brief named. **Not fixed by this pass** — re-reading the file mid-investigation found `method_calls_literals.spl:3188` **already changed to `self.error_fatal(...)` in the uncommitted working copy**, alongside two sibling `error`→`error_fatal` promotions in `expr_dispatch.spl` (lines ~1999, ~3846) — a concurrent session's live edit, not this session's. Per the "don't touch a file another session is mid-flight on" rule, this pass did not touch `method_calls_literals.spl`, `expr_dispatch.spl`, or `module_lowering.spl` (all three show as modified in `git status` from other in-flight work) and is not claiming credit for that fix — only confirming, independently, that the fix is correct and addresses a real gap. |
| `MirInterpreter` | `_pop_call_stack` | `mir_interp_ops.spl` | `mir_interpreter.spl` | **winner-is-fine** | Same reachability finding as §9/§10's `_execute_intrinsic`: no caller constructs `MirInterpreter(` outside `mir_interpreter.spl` itself, so `mir_interp_ops.spl`'s `impl MirInterpreter:` block is never loaded by any consumer found. Winner's extra `self.previous_block = frame.previous_block` restore is a strict improvement (needed for the same predecessor-block SSA-phi tracking `_execute_intrinsic`'s fix depends on). |
| `MirInterpreter` | `execute_const` | `mir_interp_ops.spl` | `mir_interpreter.spl` | **needs follow-up (low risk)** | Same reachability — loser is dead. Winner inlines an explicit `match value: case Int/Float/Bool/_` instead of loser's `self._eval_const(value)` call; not diffed further whether `_eval_const` handles strictly more/fewer cases (time-boxed out). Low risk regardless since the loser cannot execute under any consumer found. |
| `MirInterpreter` | `_call_function` | `mir_interp_ops.spl` | `mir_interpreter.spl` | **loser-has-a-fix, NOT ported — flagged as the second-highest-priority open item** | Loser (`mir_interp_ops.spl`, dead per reachability) has a deep-copy anti-corruption guard: it copies `self.locals` and `self.blocks` key-by-key into `saved_locals`/`saved_blocks` before pushing the call-stack frame, with a comment citing "module-level array variables get corrupted after `.len()` calls" and pointing at a `doc/bug/bug_report_module_var_array_init.md` (not found at that exact path this pass — closest match is `doc/08_tracking/bug/interp_module_var_array_get_method_2026-07-04.md`, not confirmed identical). Winner (`mir_interpreter.spl`) stores `self.locals`/`self.blocks` **by reference** into the `CallFrame` instead (no copy), but adds `previous_block` tracking the loser lacks. Because the winner is the *only* reachable copy (same reachability proof as every other `MirInterpreter` method), the open question is whether the corruption bug the loser's comment describes is currently reproducible against the *winner's* by-reference approach for any of `MirInterpreter`'s live consumers (the five specs listed in §10). **Not verified either way this pass** — this needs the same marker-plus-spec-run rigor §9/§10 gave `_execute_intrinsic` before any port is made; porting blind risks reintroducing the by-reference behavior's own possible upsides (e.g. intentional shared-mutation semantics) without proof either copy is actually wrong for the winner's reachable call sites. |
| `MacroRegistry` | `register_macro` | `10.frontend/parser/macro_registry.spl` | `30.types/macro_def.spl` | **likely winner-is-fine, not fully confirmed** | `macro_registry.spl` has no importer found in `src/compiler` beyond its own `parser/__init__.spl` re-export comment (no downstream consumer located in the scoped search this pass ran) — suggestive of the same orphan pattern as `higher_rank_poly_phase5b.spl`/`mir_to_llvm_helpers.spl`, in which case `macro_def.spl`'s copy (which additionally assigns a per-macro `hygiene_scope` — a real macro-hygiene feature the orphan lacks) is the sole live implementation. **Not proven to the marker-evidence bar** — the repo-wide (not `src/compiler`-scoped) importer search for `macro_registry` timed out mid-session and was not re-run; treat this verdict as high-confidence but unconfirmed. |
| `IncrementalState` | `mark_dirty` | `incremental_builder.spl` | `incremental.spl` | **dangerous, unresolved** | Confirmed both files' classes ARE loaded together in the same process: `src/compiler/80.driver/__init__.spl` re-exports `IncrementalState` from `incremental.spl` *and* separately re-exports `IncrementalBuilder`/`CompilationStatus`/etc. from `incremental_builder.spl` in the same barrel file — any consumer of `compiler.driver.*` pulls both modules in. This is the same live-collision shape as `ObjectProvider` above, not a coincidental-name-only case. Bodies are meaningfully different in behavior, not just cosmetics: `incremental.spl`'s copy marks only **direct** dependents dirty via a status dict (`self.statuses[dependent] = CompilationStatus.Dirty`, one level, no recursion); `incremental_builder.spl`'s copy marks **transitive** dependents via a recursive `self.mark_dirty(dep)` cascade over a `dirty_files` list. Whether incremental rebuilds correctly invalidate multi-hop dependency chains depends entirely on which of these two wins — a real correctness question for the incremental-build cache. **Registration order NOT traced this pass** — flagged as equally high-priority as `ObjectProvider.add_library` and `MirInterpreter._call_function`. |
| `AssocTypeProjection` | `set_resolved` | `25.traits/associated_types.spl` | `30.types/associated_types_solvers.spl` | **dangerous, unresolved — strongest name-collision-not-behavior-bug evidence found this pass** | Checked the `resolved` field's declared type in both classes: `25.traits/associated_types.spl:13` declares `resolved: HirType?` (an Option) and its `set_resolved` correctly does `self.resolved = Some(ty)`, read elsewhere via `if val Some(resolved_type) = projection.resolved:`. `30.types/associated_types_solvers.spl:300`(approx) declares `resolved: text` (a **completely different, incompatible field type** — not even `HirType`) with `self.resolved = ty` (no `Some()` wrap, correct for *its own* field type). These are two genuinely unrelated classes that happen to share a name — the field-type mismatch makes this the clearest evidence yet for the §3 caveat's suspicion. **However**, because `impl_methods` registration is keyed by the bare string `"AssocTypeProjection"` (§2), if both modules are ever loaded into the same interpreter session, one class's instances could have the OTHER class's `set_resolved` win, assigning a raw `text` into a field declared `HirType?` (or vice versa) — a type-shape violation the interpreter would not statically catch. Whether both modules are ever co-loaded (25.traits/__init__.spl re-exports the traits-package one; the types/associated_types_solvers.spl one's importers were not traced this pass) is the open question — **not resolved**, flagged for follow-up alongside the two items above. |

### Summary of new findings this pass

- **Registration-order generalization confirmed mechanistically** (not just
  empirically): one `impl Type:` block per file → registration order is a
  per-file property, so a winner/loser proof for one method transfers to
  every other method in the same twin-file pair. No pair broke this pattern
  (all twin files checked had exactly one `impl` block each).
- **Reachability (not registration race) decides 8 of the 14 pairs**:
  `QuantifierContext`/`ScopeTracker` (phase5b.spl orphaned),
  `MirToLlvm.emit_runtime_declarations`/`add_string_global`
  (mir_to_llvm_helpers.spl orphaned), `MirInterpreter._pop_call_stack`
  (mir_interp_ops.spl unreachable, same proof as `_execute_intrinsic`), and
  likely `MacroRegistry.register_macro` (unconfirmed). In all of these the
  "loser" file's `impl` block is never loaded by any consumer found in
  `src/compiler`, so there is no live registration race at all — the
  duplicate is dead weight, not a defect in practice.
- **`lower_array_lit`'s `error_fatal`/`error` divergence is a confirmed
  live correctness gap** in the same family as the `21e3950b7da` tuple-OOB
  defect, and is already being fixed by a concurrent session (found
  uncommitted in the working copy; not this pass's edit, not landed by this
  pass).
- **Three pairs are flagged as genuinely dangerous and unresolved**, all
  sharing the same shape (both twin files' classes ARE co-loaded in the
  same process, unlike the reachability-cleared pairs above):
  `ObjectProvider.add_library` (cross-imported linker↔loader),
  `IncrementalState.mark_dirty` (both re-exported from the same
  `80.driver/__init__.spl` barrel, direct-only vs. transitive dirty-marking
  — a real incremental-rebuild correctness question), and
  `MirInterpreter._call_function` (loser has an anti-corruption deep-copy
  fix for a cited module-var-array-corruption bug that the sole-reachable
  winner lacks — not verified whether the winner is actually exposed to
  that bug). `AssocTypeProjection.set_resolved` adds a fourth data point
  that the "same name, different type" pattern is real (confirmed
  incompatible field types), with the co-loading question still open.
- **No source files were edited by this pass.** The only relevant edit
  found in the working tree (`lower_array_lit`'s `error`→`error_fatal`
  promotion) was made by a different, concurrent session and was
  deliberately left untouched.

## 12. `AssocTypeProjection.set_resolved` co-loading question resolved — FALSE ALARM (2026-08-08, fifth pass)

Two `class AssocTypeProjection:` definitions confirmed at:
- `src/compiler/25.traits/associated_types.spl:17` — field
  `resolved: HirType?`, `set_resolved` does `self.resolved = Some(ty)`,
  `is_resolved()` is `self.resolved.?`.
- `src/compiler/30.types/associated_types_solvers.spl:291` — field
  `resolved: text`, `set_resolved` does `self.resolved = ty` (assigning a
  `HirType` into a `text`-typed field — itself independently suspicious,
  looks like a stubbed-out/never-typechecked variant), `is_resolved()` is
  `self.resolved != "None"`.

The field-type incompatibility (`HirType?` vs `text`) is real, confirming
§11's classification. The open question was co-loading.

**Reachability trace (same method as §9/§10/§11):**
- `25.traits/associated_types.spl` is exported from
  `25.traits/__init__.spl` and pulled in broadly: `35.semantics/resolve.spl`,
  `35.semantics/resolve_strategies.spl`, `80.driver/driver_helpers.spl`,
  `80.driver/driver_source_loading.spl`, all of `30.types/type_infer*` —
  i.e. it is live in the default driver/`native-build`/`test` pipeline.
- `30.types/associated_types_solvers.spl` (and its sibling
  `associated_types.spl`, `associated_types_defs.spl`) is imported **only**
  from within the same three-file cluster plus its own two test files
  (`associated_types_tests_def_impl.spl`,
  `associated_types_tests_resolve.spl`). `/usr/bin/grep -rln` for any of
  `associated_types_defs`, `associated_types_tests_def_impl`,
  `associated_types_tests_resolve`, or `compiler.types.associated_types`
  outside that cluster across all of `src/compiler` returns **zero** hits
  (exit 1). `30.types/__init__.spl` does not reference `associated_types` at
  all, and nothing imports `compiler.types.*` as a wildcard/barrel that
  would pull it in transitively.
- The cluster carries its own `fn main()` (`associated_types_tests_resolve.spl:314`)
  — it is a standalone demo/test script runnable only by direct invocation
  (`bin/simple run src/compiler/30.types/associated_types_tests_resolve.spl`),
  never through the compiler's own module graph. It also lives under
  `src/compiler/30.types/`, not `test/`, so it is outside the directory tree
  the default `bin/simple test` spec-discovery walks, and its test functions
  are plain `fn test_*()` (not modern-SSpec `it`/`describe` blocks), so
  nothing globs them in either.

**Verdict: confirmed-safe (never co-load).** The `30.types` variant of
`AssocTypeProjection` is orphaned dead code — unreachable from `run`,
`native-build`, `test`, or `lint`'s default pipeline. Only the
`25.traits` variant (`HirType?`-typed, the well-formed one) is ever live.
This is the same shape as the `QuantifierContext`/`ScopeTracker`/
`MirToLlvm.emit_runtime_declarations` reachability-cleared pairs in §11,
not a new type-confusion hazard. No rename performed — renaming dead code
serves no purpose and the task's own guidance is to prefer filing/leaving
over unnecessary invasive action. Recommend a follow-up cleanup bug (not
filed as urgent) to either delete the orphaned `30.types/associated_types*`
cluster or wire it in if it was meant to replace/extend the `25.traits`
version — as-is it is unreachable duplicate source, which is a maintenance
hazard (a future edit to the live 25.traits class could be "verified" by a
developer accidentally running the orphaned cluster's tests and getting a
false green) even though it is not a runtime type-confusion hazard today.
No source files edited; no build/rebuild performed.

## 13. `IncrementalState.mark_dirty` — resolved, fix ported (2026-08-08, sixth pass)

Follow-up on §11's `IncrementalState.mark_dirty` "dangerous, unresolved" row
(`80.driver/incremental_builder.spl` vs `80.driver/incremental.spl`).

**§11's behavioral characterization was backwards.** Re-reading both bodies
directly: `incremental.spl`'s `mark_dirty` (lines 77-86) is the **transitive**
one — it recurses over `self.dependents[path]` via `self.mark_dirty(dep)`,
guarded by a `dirty_files.contains(path)` early-return. `incremental_builder.spl`'s
`mark_dirty` (lines 176-183, pre-fix) was the **direct-only** one — a single
`for dependent in self.dependents[path]: self.statuses[dependent] = Dirty`
with no recursion, so a 2+-hop dependency chain left the far end stale. §11's
table had these swapped.

**Which one is correct, checked against the Rust source both files claim to
port:** `src/compiler_rust/compiler/src/incremental.rs:334-352`'s `mark_dirty`
uses an explicit worklist (`stack`/`visited`) that keeps popping and pushing
dependents until exhausted — i.e. transitive cascade. `incremental_builder.rs`
has **no `mark_dirty` of its own at all** (grepped, zero matches) — so
`incremental_builder.spl`'s copy isn't even a port of anything; it's new code
someone added when duplicating the class shape, and it silently regressed the
cascade behavior relative to the one Rust implementation both `.spl` files
cite as their source. Transitive is unambiguously correct.

**Registration-order proof (marker probe, both engine paths).** Added
`eprint("MARKER_INCREMENTAL_SPL_MARK_DIRTY")` /
`eprint("MARKER_INCREMENTAL_BUILDER_SPL_MARK_DIRTY")` to each body, then ran
a fresh driver (`bin/simple run`, not part of any spec suite) that:
1. Constructs `IncrementalState.create()` via `use compiler.driver.{IncrementalState}`
   — the name the barrel (`80.driver/__init__.spl:53`) explicitly maps to
   `incremental.spl`'s class — and calls `.mark_dirty(...)` on it.
2. Constructs `IncrementalBuilder.create()` and calls `.state.mark_dirty(...)`
   on its internally-owned `IncrementalState`.

Result: **`incremental_builder.spl`'s marker fired for both calls**;
`incremental.spl`'s marker never fired. This is a stronger finding than a
plain registration race — path 1 above is going through the exact import
(`use compiler.driver.{IncrementalState}`) that the barrel's export line
says resolves to `incremental.spl`'s class, and it still ran
`incremental_builder.spl`'s method body. An earlier probe attempt calling
`.add_dependency(...)` (a method that exists only on `incremental.spl`'s
`IncrementalState`) on the same `IncrementalState.create()` instance failed
at **semantic/type-check time** with `method 'add_dependency' not found on
type 'IncrementalState'` — confirming the collision is resolved in favor of
`incremental_builder.spl`'s class shape at the type level, not just at method
dispatch. So the two classes aren't just method-colliding; the type checker
itself treats every `IncrementalState`-named value in the barrel-importing
world as `incremental_builder.spl`'s shape (`sources`/`statuses`/`artifacts`/
`dependents`/`stats`), regardless of which module's export line a caller
wrote.

**Reachability check — this pair is currently dead code, unlike
`ObjectProvider`/`_call_function`.** `/usr/bin/grep -rn 'IncrementalState\.create\|IncrementalState(\|IncrementalBuilder\.'`
across `src/compiler` and `test/` (both `.spl` trees) turns up **zero**
callers of either class outside the two definition files and the barrel
re-export — nothing in `driver_public_compile.spl`, `native-build`, or any
spec wires this incremental-state library into a real pipeline yet. This is
a different subsystem from the object-level incremental cache flagged
elsewhere this session
(`reference_simple_native_incremental_is_a_noop_on_the_default_pipeline.md`,
`check-native-object-cache-granularity.shs`) — that one gates whole-object
reuse in `native-build`'s Rust-side cache and is unaffected by this class.
`IncrementalState`/`IncrementalBuilder` is exported library surface with no
current wiring, so today's practical exposure is zero — but it is public API
(`export use` from the driver barrel) that a future incremental-rebuild
integration would reach directly, and the direct-only body would have
silently under-invalidated multi-hop dependency chains (stale object reuse
on a file whose transitive-but-not-direct dependency changed) the moment
someone wired it up. Classified as **latent-but-real**, not urgent-today —
same "severe if reached, currently unreached" shape as several of §11's
reachability-cleared pairs, except this one's winning copy was still the
behaviorally wrong one, so it needed a code fix rather than just a
reachability note.

**Fix ported into the winning copy** (`incremental_builder.spl`, since that
is what every construction path actually executes): replaced the direct-only
body with a transitive cascade over `self.dependents`, guarded by
`self.get_status(path) == CompilationStatus.Dirty` (checked via `==` on the
`CompilationStatus` enum, confirmed to work in this build with a throwaway
probe) as the recursion's cycle-breaker, matching `incremental.spl`'s
`dirty_files.contains(path)` guard and the Rust `visited` set. Re-ran the
probe with a manually-registered 3-file chain
(`a.spl <- b.spl <- c.spl` via `register_source`, bypassing `add_source`'s
content-parser which hit an unrelated `split_whitespace` gap on `str` vs
`text` receivers in this build — not investigated further, out of scope)
and `b.state.mark_dirty("a.spl")`: `a`, `b` (1-hop), and `c` (2-hop,
transitive) all read back `CompilationStatus.Dirty` after the fix, versus
only `a`/`b` before it. `incremental.spl` was left untouched (its cascade
was already correct) other than removing its own now-redundant probe
marker. Both markers removed after verification;
`/usr/bin/grep -rn "MARKER_INCREMENTAL" src/compiler` → 0 matches;
`sh scripts/check/check-no-sabotage-residue.shs` → `PASS — 17 file(s)
checked, no residue`.

**One clobber encountered and recovered from mid-pass:** the first port edit
to `incremental_builder.spl` was silently reverted back to the pre-fix
direct-only body between the edit and the next tool call (file-state
system-reminder showed the old body verbatim) — consistent with this
session's known shared-working-copy hazard
(`feedback_dont_touch_a_file_another_concurrent_session_is_midflight_on.md`
and siblings). Re-applied the same edit and re-verified with `grep` for the
docstring text (`"transitive"`, `"section 12"`) before proceeding; the
probe run afterward confirmed the fix was live. Did not touch any file shown
as modified by another session in `git status` beyond this pair.

**Disposition:** `IncrementalState.mark_dirty` is resolved — landed
alongside this doc update. §11's row for this pair should be read as
superseded by this section (its A/B behavioral labels were reversed; the
correctness gap it flagged as "a real incremental-rebuild correctness
question" is now fixed in the copy that actually runs).

## 14. §12 correction — `associated_types_defs.spl` is text-fixture load-bearing; whole-cluster deletion is NOT clean (2026-08-08, follow-up verification pass)

§12's "confirmed-safe (never co-load)" verdict and its "recommend a
follow-up cleanup bug to delete the orphaned `30.types/associated_types*`
cluster" note scoped the reachability grep to `src/compiler` only ("outside
that cluster across all of `src/compiler` returns zero hits"). Re-running
`/usr/bin/grep -rl` for the cluster's module names across the **whole repo**
(not just `src/compiler`) finds one hit §12 missed:
`test/01_unit/compiler/bootstrap/hir_symbol_alias_owner_collision_spec.spl:18`
does `file_read("src/compiler/30.types/associated_types_defs.spl")` and
asserts the raw text contains `"type Symbol = text"` and `"export Symbol"`
(a regression check for
`doc/08_tracking/bug/stage3_selfhost_symbol_alias_conflict_2026-08-04.md`,
confirming a module-local `Symbol` alias survives untouched). That spec lives
under `test/01_unit/`, the default `bin/simple test` discovery tree, so
`associated_types_defs.spl` is load-bearing as a **text fixture**, even
though (per §12, still correct) it is never `use`-imported/compiled outside
the cluster itself.

This complicates "delete the whole cluster": `associated_types_defs.spl`
must keep existing with matching content, and the cluster's internal imports
are circular (`associated_types_defs.spl:14` does
`use compiler.types.associated_types_solvers.*`, while
`associated_types_solvers.spl:14-16` imports back from
`associated_types_defs.spl`) — so deleting `associated_types_solvers.spl`
(the file that actually contains the orphaned `AssocTypeProjection` class
§11/§12 investigated) would leave a dangling `use` clause in the file the
test depends on. That `use` is never exercised (the test only greps text,
never compiles the module), so it would not break the test, but it leaves
invalid-looking Simple source sitting in a tree that's otherwise supposed to
compile.

**Verdict, corrected:** not a clean "genuinely dead, delete it" case as §12's
recommendation implied. `associated_types_defs.spl` is referenced/load-bearing
(via the test above) and must stay; `associated_types_solvers.spl`,
`associated_types.spl`, `associated_types_tests_def_impl.spl`, and
`associated_types_tests_resolve.spl` remain unreachable from any compiled
pipeline (`run`/`native-build`/`test`/`lint`) as §12 found, but partial
deletion would strand a dangling import in the sibling the test needs.
Left the cluster untouched this pass rather than partially delete it; if
this is revisited, the safe order is (a) drop the now-unnecessary
`use compiler.types.associated_types_solvers.*` from
`associated_types_defs.spl` first, verify the two `file_read` assertions in
the spec above still pass, and only then remove the other four files.

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: STILL-OPEN (no dedup present)

The cited `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
(4311 lines) contains no first-wins dedup or duplicate-impl diagnostic —
`grep -n "first_wins|dedup|duplicate"` matches only unrelated comments
(:2529 arity check, :3272 receiver re-lowering, :3582 literals duplication).
Nothing implements or reports duplicate impl-method detection, consistent with
the reported silent first-win. Owner path: src/compiler/50.mir/**.
