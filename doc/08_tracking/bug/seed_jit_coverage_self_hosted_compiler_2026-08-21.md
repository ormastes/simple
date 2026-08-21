# Seed JIT coverage on the self-hosted compiler: the premise was wrong — there is no per-function fallback

**Date:** 2026-08-21
**Status:** OPEN (census landed; both blockers filed as follow-ups)
**Related:** `seed_interpreter_raw_throughput_2026-08-21.md` (d2181a9afe8),
`lint_dejits_whole_program_span_struct_collision_2026-08-18.md`

## The claim under test

`seed_interpreter_raw_throughput_2026-08-21.md` states that `bin/simple run` is a
**hybrid**: `compiler/src/compilability.rs` classifies each function and routes it
to Cranelift JIT (~10-25 ns/op) or to interpreter fallback (~100-1000 ns/op) by
`FallbackReason`. The proposed work was to measure which `FallbackReason`s cover
the most executed time in the self-hosted compiler and widen Cranelift lowering
for the top one or two.

**That premise is false for this lane, and the proposed work would have been
worthless.** There is no per-function split on the path `bin/simple lint` takes.
Every de-JIT here is **whole-module and whole-program**, and
`compilability::analyze_module` is never called at all.

## Evidence

`compilability::analyze_module` has exactly three non-test call sites, all in
`compiler/src/pipeline/execution.rs` (:564, :716, :961), all
`CompilabilityMode::AotNative` — the `compile --native` lane. The JIT run path,
`driver/src/exec_core.rs::run_file_jit`, calls `apply_hybrid_transform` **only**
for unresolvable externs (:1109); it never consults the classifier. So no
`FallbackReason` is ever computed for `bin/simple run`/`lint`.

Instrumented with the new census (below), a real
`lint src/compiler/80.driver/driver_types.spl` emits exactly **one** line — one
decision for the whole program, not a per-function histogram:

| lane | census output |
|---|---|
| default | `de-jit whole-module reason=cli-args-substring path=src/app/cli/lint_entry.spl` |
| `SIMPLE_EXECUTION_MODE=jit` | `de-jit whole-module reason=jit-compile-error path=src/app/cli/lint_entry.spl` |

There is no top-20 fallback-function table and no reason histogram to report,
because neither exists on this lane. A census keyed on `FallbackReason` would
have measured a code path that never executes.

## The two real blockers, in series

**Gate 1 — `cli-args-substring` (`exec_core.rs::interpreter_preference_reason`).**
`should_prefer_interpreter_for_source` diverts a source to the interpreter
*before the JIT is ever attempted* when the **entry file text contains** any of
`get_cli_args`, `rt_cli_get_args`, `sys_get_args`, `rt_get_args`, or `std.cli`.
`src/app/cli/lint_entry.spl:6` is `use std.cli.cli_util (get_cli_args)`. Every
pure-Simple CLI app parses argv, so **essentially the entire self-hosted compiler
surface is diverted by a substring match**. It is a plain `source.contains`, not
a semantic check, and it inspects only the entry file, never imports.
Escape hatch: setting `SIMPLE_EXECUTION_MODE` at all bypasses it (:1415).

**Gate 2 — `jit-compile-error`, the duplicate `Span` struct.** With gate 1
bypassed, HIR lowering fails outright:

```
HIR lowering error: Cannot infer field type: struct 'Span' field 'end_pos'
  (declared fields: start, end, line, col, file, length) [in src/app/cli/lint_entry.spl]
  ... whole module dropped to the interpreter (expect ~100-1000x slowdown).
```

Two `Span` structs collide in the flattened import namespace:

- `src/compiler/00.common/diagnostics/span.spl:7` — `start, end, line, col, file, length`
- `src/compiler/10.frontend/core/lexer_types.spl:12` — `start, end_pos, line, col`

`load_module_with_imports` flattens every import into one bare-name namespace, the
diagnostics `Span` wins, and every `.end_pos` in the lexer fails inference.

The duplicate-struct sidecar (`SIMPLE_JIT_DUP_STRUCT_FEED`,
`resolve_duplicate_global_field_variant`) is **not** the fix and is correctly
gated off. Its resolution is by field-name agreement across variants, with no
receiver type: `length` matches only the diagnostics variant, so it resolves to
index 5, and a lexer `Span` receiver (4 fields) then reads slot 5 as garbage.
That is the documented miscompile in `exec_core.rs:1030-1053`. Name-based
resolution cannot be made sound without receiver types.

Gate 2 is not unique to lint — `info` hits a *different* whole-module HIR error
(`cannot resolve import app.package.registry.config`), so each entry point has
its own blocker. This is a chain, not one bounded fix.

## What landed

`driver/src/exec_core.rs`: a level-gated de-JIT census, `SIMPLE_JIT_COVERAGE=1`,
default off. `should_prefer_interpreter_for_source` is split into
`interpreter_preference_reason` (returns the *named* reason) plus a reporter;
markers also fire on `jit-compile-error` and `jit-panic`. Previously gate 1 fired
with **no diagnostic at all**, which is exactly why this cost sat unmeasured —
the `[jit-fallback]` warning only prints when the JIT was actually attempted.

Three mechanism tests pin the reason strings (`..._names_the_cli_args_substring_gate`,
`..._is_none_for_an_ordinary_source`, `..._distinguishes_the_shs_gate`). The first
fails pre-fix: `interpreter_preference_reason` did not exist and the gate returned
a bare bool, so the reason could not be asserted.

## Follow-ups (not done here)

1. **Rename the lexer `Span` to `LexSpan`** in `src/compiler/10.frontend/core/`.
   Scope: 19 `.spl` files mention `end_pos`/`lex_span_*`; 26 files under
   `10.frontend` reference `Span`. This is the only *sound* fix for gate 2 and is
   a `src/compiler` change, so it belongs to the parser lane.
2. **Replace gate 1's substring test** with a real check, or make `get_cli_args`
   JIT-safe. Until gate 2 is cleared this changes nothing measurable, so it should
   be sequenced second.
3. Only after both: revisit whether a per-function `FallbackReason` census is
   worth building. It is inert until a module survives HIR lowering.

## Wall time (secondary — box loaded, ~44s user either way)

`lint src/compiler/80.driver/driver_types.spl`: 2m12s default, 1m26s with
`SIMPLE_EXECUTION_MODE=jit` — but the latter still ends in the interpreter after a
failed JIT attempt, so the difference is scheduling noise on a contended box, not
a JIT win. The census delta is the primary evidence; no JIT speedup was obtained,
because no module was successfully JIT-compiled.

---

## Update 2026-08-21 — lint is ON the JIT; worker is blocked on the closure ABI

Follow-ups 1 and 2 above are done, plus eleven further blockers found by
iterating. Measured with `bin/simple` (the deployed seed), target
`src/compiler/80.driver/driver_types.spl`:

| stage | wall | lane actually taken |
|---|---|---|
| interpreter (`SIMPLE_EXECUTION_MODE=interpret`) | 29.7s | interpreter |
| jit, before any fix | 23.8s | **interpreter** (silent de-JIT) |
| jit, after the `Span` rename only | 38.3s | interpreter (3 codegen stub fallbacks) |
| jit, after the `std.path` fix | **11.0s** | **JIT** |

2.7x on lint, and the verdict is byte-identical (0 errors, 8 warnings,
`Lint passed`). Pinned by `scripts/check/check-lint-runs-on-jit.shs`.

### The blocker chain, in the order the JIT hit it

Every entry below is the SAME defect class: the JIT flattens all imports into
one bare-name namespace, so two same-named types anywhere in the whole-program
closure collide and HIR lowering hard-fails with `Cannot infer field type:
struct 'X' field 'f'`, de-JITing the ENTIRE program with no user-visible error.

1. `Span` — lexer (`start,end_pos,line,col`) vs diagnostics
   (`start,end,line,col,file,length`). Lexer one renamed `LexSpan`. Five
   compiler files imported `Span` from `lexer_types` while *constructing* it
   with diagnostics fields; those imports were repointed.
2. `path_separator`/`search_path`/`path_find_all` in `src/lib/*/env/paths.spl`
   used deprecated `import std.path` + module-qualified `path.join2(...)`.
   Cranelift has no module objects: `GlobalLoad: unresolved identifier 'path'`.
   3 failed bodies de-JIT the whole program. Converted to named `use` imports.
3. `Type` — blocks placeholder vs parser AST -> `BlockType`.
4. `LoopInfo` — two structs vs `loop_detect`'s class -> `VectorLoopInfo`,
   `SimdLoopInfo`.
5. `Bitfield`/`BitfieldField` -> `ResolvedBitfield`/`ResolvedBitfieldField`.
6. The whole treesitter subsystem annotated token spans as `Span` and called
   `span_new` (which builds a DIAGNOSTICS span) while reading `.end_pos`
   -> `LexSpan` + `lex_span_new`.
7. `JitStats` -> `TieredJitStats`.
8. `InstantiationRecord` (3 defs) -> `JitInstantiatorRecord`,
   `LoaderInstantiationRecord`, `JitContextRecord`.
9. `CompiledModule` -> `CraneliftCompiledModule`.
10. `TraitDef`/`TraitBound`/`TraitBoundKind` -> `Solver*`.
11. `CompiledUnit` (3 defs) -> `TemplateCompiledUnit`, `EngineCompiledUnit`.
12. `SmfHeader` -> `SmfReaderHeader`.

### Remaining chain for `run src/app/cli/native_build_worker.spl`

After 12 the worker clears HIR lowering entirely and reaches codegen, where it
hits a **different and much larger** blocker:

```
Cranelift JIT compile: Module error: function 'SdnBackendImpl.is_allowed'
creates a lambda/closure; the JIT closure ABI does not tag-box lambda arguments
or results and is incompatible with the runtime's RuntimeClosure layout, so JIT
would return wrong values or crash; deferring to interpreter
```

This is a **whole-module** bail on ANY function anywhere in the closure that
creates a lambda. `HirLowering.format_type` was the first; its three
`types.map(self.format_type(_))` placeholder-lambdas were rewritten to an
explicit `format_types` loop, which merely advanced the error to the next
lambda. There are hundreds of such functions in the compiler + stdlib closure,
so rewriting them one by one is neither tractable nor correct.

**The real fix is seed-side: make the JIT closure ABI tag-box lambda arguments
and results so it matches the runtime's `RuntimeClosure` layout.** Until then
`native_build_worker` cannot reach the JIT. Recorded here rather than worked
around, per the "don't silently normalise a workaround" rule — the
`format_types` loop carries an in-source comment pointing back at this record.

### Still-open duplicate-name census (not in the worker's closure yet)

`src/compiler` alone still has **48** duplicate STRUCT names whose field sets
differ (the census excludes classes and enums, which collide identically —
`LoopInfo` above was exactly such a struct-vs-class case, so the true number is
higher). Twelve were cleared here because the worker's closure reached them.
Reproduce the census with a `^struct X:` scan over `src/compiler`. Each one is a
latent whole-program de-JIT for whichever entry point first pulls both halves
into one closure.

---

## Update 2026-08-21 (later) — the untyped indirect call is fixed; the unboxed closure ABI is now admitted for the self-contained case

The previous section closed with "the real fix is seed-side: make the JIT closure
ABI tag-box lambda arguments and results". That framing was one step too far. The
first attempt was reverted not because boxing was missing but because
**`MirInst::IndirectCall` carried `return_type = ANY` / `param_types = [ANY]` for
every untyped lambda**, and no value encoding at an untyped boundary can be right
for both an i64 and an f64. That is now fixed, and with real types on the boundary
the *self-contained* case needs no boxing at all.

### Typing changes

- `hir/lower/expr/operators.rs` — **numeric promotion.** `lower_binary` typed the
  result as `left_hir.ty`, so `x * 1.5` with an integer `x` was typed I64 while
  codegen's binary arm coerces a mixed int/float pair to FLOAT. The HIR type was a
  plain lie about the machine value. Now: both sides numeric scalars and exactly
  one a float ⇒ the float type. Deliberately scoped so string concat (`"s" + n`)
  and ANY operands are untouched.
- `mir/inst_enum.rs` — `ClosureCreate` gains `return_type`, populated in
  `mir/lower/lowering_expr_async.rs` from the lambda BODY's HIR type.
- `mir/closure_call_types.rs` (new) — an intraprocedural MIR pass, run at the end
  of `lower_module`. It follows a closure from its `ClosureCreate` through the
  `Store`/`Load` pair a `val` binding lowers to, and stamps the lambda's real
  signature onto the `IndirectCall` sites that consume it. Poisons a local that
  holds two conflicting closures; poisons a call site whose caller argument types
  disagree with the types the outlined body was compiled with.
- `mir/lower/lowering_expr_call.rs` — the signature fallback records the CALLER's
  argument types instead of a row of `ANY`, which is what makes that
  disagreement check possible.
- `codegen/shared.rs` — a lambda's outlined function had `return_type` hardcoded
  to I64. It now declares the lambda's real return type, so the outlined body's
  Cranelift signature and the `IndirectCall` signature agree by construction.

### Why the parameter-side lie matters, and how it is contained

HIR defaults an UNDECLARED lambda parameter to I64. `\x: "v" + x` called with a
text therefore compiles a body that does i64 arithmetic on a string handle — under
the JIT it printed `v4483685820545` instead of `va`. That is a real pre-existing
miscompile, not an ABI question: the poisoning rule above detects exactly this
(caller arg type ≠ compiled param type) and leaves the boundary `ANY`, which the
admission guard then refuses. Fixing the parameter inference itself is a separate,
larger job and is NOT done here.

### The ABI, and what is admitted

`codegen/jit.rs::first_unsupported_lambda` replaces the blanket
"any `ClosureCreate` anywhere ⇒ refuse the whole module" bail. Two conventions
exist and only one is admitted:

1. **JIT-internal** — the closure is called back by an `IndirectCall` in the same
   function. Both halves are emitted by this backend and now agree by
   construction, so **no tag-boxing is needed**; the values never leave JIT code.
2. **Runtime-facing** — the closure is passed as an argument (`Array.map`),
   stored into a heap object, captured by another closure, or returned. Whoever
   calls it goes through the runtime's `RuntimeClosure` layout and its
   all-`RuntimeValue` convention, which is not what `compile_closure_create`
   builds. **Still refused, and this is the remaining blocker.**

Also refused: any boundary type that is not carryable unboxed
(`codegen::jit_closure_abi_supports` — I64/F64-width only). `TypeId::BOOL` lowers
to `i8` and **SIGSEGV'd** the process on `print(f(32))` for `\x: x > 1`; that is
why the predicate exists rather than a blanket allow.

The guard also had to learn that a lambda's parameter reuses the PARENT's local
slots — HIR truncates the lambda's locals after lowering the body, so in
`val f = \x: ...` both `x` and `f` are local index 0 — which made the body's read
of its own parameter look identical to a load of the closure.
`outlined_body_block_ids` excludes the not-yet-outlined body blocks from both the
pass and the guard.

### Measured (differential, JIT vs interpreter, 8 lambda fixtures)

| fixture | lane taken | result |
|---|---|---|
| `\x: x*10`, `\a,b: a+b` | **JIT** | identical |
| capturing a mutable local | **JIT** | identical |
| lambda called inside `fn`, result returned | **JIT** | identical |
| `\x: x*1.5` called with `4.0` | fallback (poisoned ANY) | identical |
| `\x: "v"+x` called with `"a"` | fallback (poisoned ANY) | identical |
| `\x: x>1` (BOOL result) | fallback (unsupported type) | identical |
| `xs.map(\x: x*3)` | fallback (runtime-facing) | identical |
| nested lambda capturing a lambda | fallback (runtime-facing) | identical |

No wrong answers in any lane. The `test/fixtures/engine_differential` corpus is
unchanged: 10/12 SAME, and the 2 DIFFs (`i64_boundary_values`,
`utf8_slice_boundary`) are the two pre-existing, already-filed ones.
`cargo test -p simple-compiler --release --lib`: same 52 failures as baseline,
none closure- or float-related.

### The worker probe could not be run — a DIFFERENT, PRE-EXISTING blocker

`SIMPLE_JIT_COVERAGE=1 native-build --source src/app --entry-closure --entry
src/app/cli/bootstrap_main.spl` fails before reaching a single `[build] parse`
line, with

```
error: semantic: nil is forbidden by the non-optional return contract of 'env_get'
```

**This is not caused by anything above.** Attributed by building a seed from HEAD
content for exactly the files this change touches (leaving every other
worktree-local modification in place) and running the identical command: it fails
identically, `env_get=11 parse=0`, rc=1. So there is no `dt=` table to report and
no evidence yet about whether the worker stays on the JIT — the worker never gets
that far on a locally-built seed in this tree. That blocker must be cleared before
the closure-ABI question can even be asked of the worker.

### Remaining, in order

1. The `env_get` non-optional-return blocker above — until it is fixed the worker
   lane is unmeasurable from a locally-built seed.
2. The runtime-facing convention: `rt_closure_new`/`rt_closure_set_capture`
   allocation plus tag-boxed arguments, results and captures on both sides, so a
   lambda handed to `Array.map` can be JIT-compiled. This is what actually
   unblocks `native_build_worker`, whose bail was on `SdnBackendImpl.is_allowed`.
3. Undeclared lambda parameter types (defaulted to I64) — currently detected and
   routed to the interpreter rather than inferred.
4. `TypeId::BOOL` (and other sub-register types) across a closure boundary.
