# Family sweep: disc-guarded fast paths that skip trailing bookkeeping

Date: 2026-08-01
Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
Related: `064d40e5896` (the two originally proved instances)

## The defect shape

A dispatcher runs a discriminant check to shortcut a `match`, handles the
common case, and `return`s early -- **before** the trailing bookkeeping the
fall-through path performs on its way out. Skipped bookkeeping
(`mark_*`, `register_*`, `define_*`, `record_*`, counter bumps, cache inserts)
produces a *silent wrong answer*, never an error.

Both originally proved instances made **every user-defined function call return
0** under `native-build --backend llvm`, with exit 0 and a real ELF.

## Sweep 1 -- trailing-bookkeeping-after-dispatch: FAMILY CLOSED

Predicate: a `match` dispatch whose *immediately following* statement at the
same indent is a bookkeeping call, in a function that also has an early
`return` above the match. Scanned all of `src/compiler/**` (analyzer:
`scan_trailing.py`, `/usr/bin/grep` pinned throughout -- default `grep` here is
ugrep).

**Exactly 3 dispatch+trailing-bookkeeping sites exist in `src/compiler`:**

| Site | Early returns above? | Verdict |
|---|---|---|
| `70.backend/backend/_MirToLlvm/core_codegen.spl:536` `translate_instruction` -> `mark_instruction_dest_defined(inst)` | YES (2: `Const`, `Copy`) | the proved family; hardened below |
| `70.backend/backend/llvm_ir_builder.spl:182` `start_function_opt` -> `self.emit(...)` | NO | provably-equivalent -- nothing can skip the trailing emit |
| `70.backend/backend/llvm_ir_builder.spl:202` `start_function_with_attrs` -> `self.emit(...)` | NO | provably-equivalent -- same reason |

`translate_instruction` has exactly two early-return fast paths, and both are
now accounted for:

- **`Const`** -- `translate_const` self-marks (`defined_locals[dest_id] = true`,
  core_codegen.spl:943). Provably equivalent. Note `mark_instruction_dest_defined`
  does not even list `Const`, so the call is a no-op for this arm.
- **`Copy`** -- was the proved defect (instance 2); `translate_copy_move` now
  self-marks at :1010.

**Conclusion: the exact shape is a closed family of one defect. No siblings
remain.** PROVED by exhaustive scan, not sampling.

### Hardening landed

Correctness of `translate_instruction` previously depended on an *implicit*
invariant -- "every fast-path callee happens to self-mark". That invariant is
invisible at the fast path itself and was already broken twice. Both fast paths
now call `self.mark_instruction_dest_defined(inst)` before returning, making
them structurally identical to the fall-through. The call is idempotent
(`defined_locals[x] = true`), so it composes with the callees' self-marking.

## Sweep 2 -- `case Some` on a nullable: PREMISE FALSIFIED

The brief's premise was that `case Some` **never** matches a nullable `T?`, so
every such site is a latent silent bug. **That is false as a general rule**, and
a blanket rewrite of all such sites would not have been justified.

Measured (PROVED, in-situ and standalone):

- **Standalone** (`simple_seed run`): `case Some` on a nullable matched
  correctly for `i64?`, `text?`, class-typed, **struct-typed** (value type),
  parameter-sourced, and match-expression-sourced nullables, in both inline
  (`case Some(x): e`) and indented arm forms. 9/9 shapes correct.
- **In-situ, inside a compiler module**
  (`80.driver/driver_build/incremental.spl:123`, `backend: text?`):
  `match_arm=llvm ifval=llvm` -- **matched correctly**.
- **In-situ at the known-failing site**
  (`20.hir/hir_lowering/statements.spl`, `rt_val: Expr?`):
  `match_some=0 ifval=1 isnil=false`, 7/7 evaluations. **Diverges.**

So the discriminator is narrow. The failing nullable is one produced by
**enum-payload extraction inside a disc-guarded fast path**, where the extern
lies about nullability:

```
extern fn rt_enum_payload(value: StmtKind) -> Expr    # payload is really Expr?
```

The raw payload word that comes back does not carry the representation
`case Some` tests for, while `if val`'s nil check handles it. The predicate is
therefore *"nullable sourced from `rt_enum_payload`"*, not *"nullable"*.

### Enumeration of the candidate population

420 `match` sites in `src/compiler` have a `case Some`/`case None` arm. Resolving
each scrutinee's declared type: **24 NULLABLE**, 4 `Option<T>` (correct by
construction), 12 non-optional, 380 unresolved-by-static-scan.

All 24 NULLABLE sites were instrumented simultaneously with a shadow
`case Some` vs `if val` comparison and a real `native-build` was run.

**Result: 0 divergences -- but only 2 of the 24 sites actually executed.**
This was verified explicitly by re-running with the comparison forced
unconditional and counting per-site hits; without that check the "0 divergences"
result would have been vacuous.

| Status | Count | Sites |
|---|---|---|
| PROVED correct in-situ | 2 | `80.driver/driver_build/incremental.spl:123,126` |
| **Not exercised by this workload -- UNPROVEN, needs-owner** | 22 | vhdl (`vhdl_codegen_helpers`, `vhdl_entity_compile`, `vhdl_validation`, `_VhdlProcess/process_codegen` x3, `vhdl/vhdl_call_lowering` x2), riscv/aarch64 isel (`isel_aarch64`, `isel_riscv32` x2, `isel_riscv64` x2), `50.mir/mir_lowering_stmts.spl:54`, `50.mir/_MirLoweringExpr/method_calls_literals.spl:2302`, `50.mir/_MirLoweringExpr/switch_operators_calls.spl:1929`, `00.common/di.spl:208`, `15.blocks/blocks/registry.spl:121`, `80.driver/init.spl:208`, `80.driver/layout_recorder.spl:191`, `80.driver/smf_serialization.spl:154` |

These 22 are **deliberately not touched**: none matches the proved-broken
predicate (none is sourced from `rt_enum_payload`), and none could be exercised
to demonstrate a divergence. They need a vhdl/riscv/aarch64 workload to settle.
Rewriting them blind would be unverifiable churn.

`statements.spl` itself was re-checked for siblings of instance 1: its other
disc-guarded fast paths (`Val`, `Var`, `Assign`, `Expr`) contain **no**
`case Some` at all -- they already use `if val`. Clean.

## Evidence (all on built-and-run ELFs, `SIMPLE_BINARY`/`bin/simple_seed`)

Isolated A/B lane: `bin/simple_seed native-build` loads `src/compiler/**/*.spl`
**relative to CWD** (PROVED by sabotage), so a scratch extraction of pristine
origin `02f5777565` is a complete, non-vacuous A/B lane. The shared working copy
was never touched.

Harness non-vacuity: sabotaging `statements.spl` alone flips
`f2a=111 f2b=222 fact=120 outer=120` -> `f2a=0 f2b=0 fact=0 outer=0`.

2x2 matrix for the instance-2 defect and the hardening, using a workload that
actually contains a pure-Copy return (`val z = y; return z`):

| instance-2 fix | hardening | `tail` / `tail_copy` |
|---|---|---|
| absent | absent | **0 / 0 (RED)** |
| absent | present | 6 / 12 (GREEN) |
| present | present | 6 / 12 (GREEN) |

The hardening therefore independently closes the hole.

**Trap recorded:** the first attempt at this control used a program with no
pure-Copy return (`ret.spl`) and came back GREEN in the "neither fix" cell --
a vacuous control that would have "proved" the hardening load-bearing for the
wrong reason. `tail`/`tail_copy` are the discriminating cases.

Family sweep, all GREEN and byte-identical before/after the hardening:
`five=15 bool_t=true bool_f=false f64=5.0 text=hi-x struct=7,8 fact=120
nested=22 tail=6 tail_copy=12 method=105` -- 5-arg calls, `bool`/`f64`/`text`/
struct-by-value returns, recursion, nested calls, class methods, and both
`return` and bare-tail forms.

## Open question (still INFERRED)

Whether the JIT and interpreter lanes shared instance 1. They use the same HIR
lowering, so they very likely did, but this was not measured here.

## Probes

Both existing level-gated probes were used rather than adding new ones:
`SIMPLE_MIR_RET_TRACE=1`, `SIMPLE_LLVM_RET_TRACE=1`. All temporary
instrumentation was removed; the scratch tree was verified byte-identical to
pristine origin afterwards.
