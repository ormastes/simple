# Audit: seed-only fixes (2026-08-08 session) vs pure-Simple compiler counterpart

Per CLAUDE.md: `src/compiler_rust/` is bootstrap-seed-only; `src/compiler/`
(numbered layers 00-99, pure Simple) is the real compiler. This audits five
fixes landed this session to determine which have a working pure-Simple
counterpart and which are seed-only gaps.

**Verification path for gaps below:** the pure-Simple compiler `.spl` source
is LIVE under `bin/simple test`/`bin/simple run` via the seed's interpreter —
a pure-Simple fix can be behavior-tested through the seed interpreter *before*
Stage 3 self-host is unblocked. No need to wait on the Stage-3 blocker to
verify a `src/compiler/` change.

## Table

| Fix | Seed SHA | Seed path touched | Pure-Simple path | Status |
|---|---|---|---|---|
| Impl-method owner tagging (RC1, coverage `<entry>`) | `b6a43042` | `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs` | No equivalent exists | **seed-only gap, but narrower than it looks — see Finding 1** |
| Entry-script fn owner `<entry>` fallback (RC2) | `40fa02ee` | `src/compiler_rust/compiler/src/interpreter_module/interpreter_eval.rs` + `coverage_helpers.rs` | No equivalent exists | **seed-only gap, but narrower than it looks — see Finding 1** |
| JIT named-fn-as-value guard (T7) | `45e0e8d6` | `src/compiler_rust/compiler/src/codegen/jit.rs` (`first_named_fn_value_load`) | No JIT/Cranelift-style codegen exists in `src/compiler/` at all | **seed-only by design — see Finding 2** |
| Extern-fn-as-value JIT gap (noted, not yet fixed even in seed) | `c7a07467` (doc-only note) | same `jit.rs` path, unfixed | Same as above — no analog | **seed-only by design — see Finding 2** |
| `rt_file_is_char_device` | `66959c6b` | C runtime + interpreter dispatch + JIT/AOT text-arg marshaling | `src/compiler/50.mir/text_extern_abi.spl:43` (ABI mirror) + `src/lib/nogc_sync_mut/io_runtime.spl:52,245,250` (extern decl + wrapper) | **already-mirrored, complete** |
| Span-bridge SIMD intrinsics (`fill_span`/`copy_span`) | `a399483d` | (this fix already targeted `src/compiler/`) | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1203` + `src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl:180-181` | **already-mirrored, complete** |
| Blend-span SIMD kernels (`blend_span`/`blend_const_span`) | `796d8484` | (this fix already targeted `src/compiler/`) | same two files, lines 1203 and 182-183 | **already-mirrored, complete** |

## Finding 1 — coverage owner-tagging architecture doesn't exist in pure-Simple at all

The pure-Simple interpreter (`src/compiler/10.frontend/core/interpreter/eval.spl`)
has its own, much more primitive coverage-instrumentation path:

```
extern fn rt_coverage_enabled() -> bool
extern fn rt_coverage_decision_probe(file: text, line: i64, decision_id: i64, taken: bool)
var coverage_counter: i64 = 0

fn record_decision(file: text, line: i64, taken: bool):
    if rt_coverage_enabled():
        coverage_counter = coverage_counter + 1
        rt_coverage_decision_probe(file, line, coverage_counter, taken)
```

The **only** call site is `eval.spl:492`: `record_decision("eval", eid, taken)`
— the `file` argument is a hardcoded literal `"eval"`, not derived from any
per-module or per-impl-method owner tracking. There is no
`CURRENT_EXEC_MODULE`, no `FUNCTION_MODULE_OWNER`, no `tag_methods_owner`/
`tag_function_module_owner`, no `<entry>` sentinel, and no `Node::Impl` owner
registration anywhere in `src/compiler/` (confirmed by `git grep` across the
whole tree — zero hits for any of those identifiers). `git grep` for
`current_coverage_file` also returns nothing under `src/compiler/`.

**Conclusion: this is not "the pure-Simple path has the same <entry> bug and
needs the same one-line fix."** It's a strictly bigger gap: pure-Simple's
interpreter never attributed decision-coverage rows to their real source file
at all — every decision probe from the self-hosted interpreter is filed under
the literal string `"eval"`, unconditionally, regardless of module or
impl-method. Both RC1 (impl-method owner tagging) and RC2 (entry-script owner
fallback) are downstream refinements of a module-owner-attribution mechanism
that must first be *built* in pure-Simple, not a bug that can be patched with
an equivalent one-line diff.

**Scoped follow-up work** (not attempted here, per task scope):
1. Add a module/file-owner tracking mechanism to `src/compiler/10.frontend/core/interpreter/eval.spl`
   (or wherever function/method dispatch already carries a defining-module
   reference — check `eval_tables.spl`'s func table, which likely already
   stores the source file per function since it must resolve overloads).
2. Thread that owner through `record_decision`'s `file` parameter instead of
   the hardcoded `"eval"` literal.
3. Only once that exists does an RC1-equivalent (impl-block methods getting
   tagged like Class/Struct/Enum methods) or RC2-equivalent (a stable
   `<entry>`-style bucket for genuinely-unowned top-level entry-script code)
   become meaningful bugs to fix.
4. Verify via `bin/simple test` / `bin/simple run` against the seed
   interpreter (pure-Simple `.spl` source is live there — no Stage-3 wait
   needed), using the same engine2d_baremetal_core coverage-sparsity repro
   the seed-side RC1 doc used as its A/B probe.

## Finding 2 — no JIT codegen exists in pure-Simple; the T7/extern-fn gap has no analog

`src/compiler/` has no Cranelift-style JIT compiler. The only "jit"-named
files are `src/compiler/99.loader/jit_context.spl` and `jit_instantiator.spl`,
which are module-loader/instantiation-caching machinery (tracking a
`"jit_time"` stat), not a code-generation backend. The pure-Simple compiler's
actual code-generation path is `src/compiler/50.mir/` (MIR lowering) →
`src/compiler/70.backend/` (LLVM IR emission, i.e. an AOT/LLVM path, not an
in-process JIT). There is no `GlobalLoad`-shaped MIR instruction, no
`compile_indirect_call`, and no "static method reference" fallback concept
under `src/compiler/50.mir/` or `src/compiler/70.backend/` (all zero hits by
`git grep`).

**Conclusion:** `45e0e8d6`'s `first_named_fn_value_load` guard and
`c7a07467`'s noted extern-fn gap are specific to the Rust seed's bespoke JIT
engine's closure-ABI representation. Since pure-Simple has no equivalent
code-generation engine with that ABI shape, there is no parallel bug for it to
have — **this is seed-only by design**, not a gap. (Whether pure-Simple's
LLVM-IR path has its *own*, structurally different bug around function values
used as call targets is a separate, unasked question — worth a follow-up scan
of `src/compiler/70.backend/backend/_MirToLlvm/` for indirect-call codegen if
named-function-as-value usage is exercised through the LLVM/AOT path, but it
is not a "mirror this fix" task since the fix's mechanism doesn't transfer.)

## Summary

- **Already-mirrored, complete (3):** `rt_file_is_char_device` (`66959c6b`),
  span-bridge intrinsics (`a399483d`), blend-span kernels (`796d8484`) — all
  three landed directly in `src/compiler/` this session and were confirmed
  present in both the MIR type-registration site and the LLVM `declare` site.
- **Seed-only by design, no analog exists (2):** JIT named-fn-as-value guard
  (`45e0e8d6`) and the noted extern-fn JIT gap (`c7a07467`) — pure-Simple has
  no JIT codegen engine to carry the bug.
- **Gap needing pure-Simple work, larger than "mirror the fix" (2):**
  impl-method owner tagging (`b6a43042`) and entry-script owner fallback
  (`40fa02ee`) — the underlying owner-attribution mechanism doesn't exist yet
  in `src/compiler/10.frontend/core/interpreter/eval.spl`; today every
  decision-coverage row from the pure-Simple interpreter is filed under the
  literal `"eval"`. Scoped follow-up steps are listed under Finding 1.
