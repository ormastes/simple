# iso ownership-transfer sites still missing MIR `Move` (WP-M audit)

**Status:** CLOSED — all of items #1, #2, #3 (plus the array/dict/`.push()`
collection-store follow-up) now emit real Move facts. Item #4 remains
unreachable per WP-S's 2026-08-07 finding (unchanged, see below).
**Lane:** WP-M (2026-08-06); items #2/#3/collections closed by a concurrent
WP-F lane (commit `6a53442fbd1`, checker terminator wiring commit
`63dc29b11a2`); item #1's remaining lowering half closed by WP-F
(2026-08-07, this update).

**Update 2026-08-07 (WP-F, item #1 — returning an iso value):** Closed both
halves.
- The **checker** half was already closed by commit `63dc29b11a2`
  ("detect use-after-move through call operands and terminators"): `mod.spl`
  gained `analyze_terminator` + `record_operand_use`, which reads whatever
  operand kind (`Copy`/`Move`) a `Ret`/`If`/`Switch`/`CallTerminator`
  terminator carries.
- The **lowering** half needed two sites, not one — the bug doc's original
  description only named the implicit tail-expression return
  (`_MirLowering/function_lowering.spl`); there is a second, independent site
  for an *explicit* `return expr` statement
  (`_MirLoweringExpr/expr_dispatch.spl`'s `lower_return_expr`). Both now emit
  a synthetic `emit_move(fresh, tail_local_or_result)` ahead of the `Ret`
  terminator, gated on `mir_hir_type_is_isolated(self.find_local_hir_type(...))`,
  mirroring the already-landed call-argument/field-store pattern.
- **Why the lowering half is not redundant with the already-working checker
  half:** `record_use` (what a bare `Copy` operand on `Ret` triggers) only
  *checks* `moved_now`, it never *adds* to it — only `record_move` does. The
  simple `val c = a; a` (moved-then-returned, same block) case was already
  caught by the checker alone (`record_use` sees the earlier `Move`
  instruction's fact). But an **early `return a` inside one branch of an
  if/else**, followed by a use of `a` in the fall-through/merge block, was
  NOT caught without the lowering fix: the checker's `analyze_mir_borrows`
  walk is a purely linear, already-documented-as-correct-and-out-of-scope
  (SF1, `borrow_graph.spl`) forward walk over `func.blocks` in array order,
  not CFG-path-sensitive — the early-return branch's `a` needs to land in
  `moved_now` (via a real `Move` instruction) for the later block's read to
  be flagged. Sabotage-verified this exact distinguishing scenario, not just
  the same-block case (see Evidence trail below).
- Proof: `test/01_unit/compiler/borrow/iso_move_return_spec.spl` (new, 5/5).
  Sabotage (real run, `bin/simple test`):
  - Reverting `function_lowering.spl`'s fix alone: **still 3/3 green** on the
    tail-return cases — confirms the checker's existing `record_use`-on-Copy
    already covers the simple same-block case, so this half is a
    completeness/consistency fix (matches every other transfer site emitting
    a real Move), not a detection fix, for that narrower shape.
  - Reverting `expr_dispatch.spl`'s explicit-`return` fix (with
    `function_lowering.spl`'s fix in place): `5 total, 4 passed, 1 failed` —
    exactly the new "early return in an if-branch" case goes red, proving
    that site IS load-bearing for detection. Reverted the sabotage: back to
    `5 total, 5 passed, 0 failed`.

**Update 2026-08-07 (WP-F0, commit `3f79f98cc9d97bf902db5da7d32e215e297b4ebf`):**
Item #4's mutual-exclusivity blocker is fixed. `function_lowering.spl`'s
second `match param.type_.kind:` (the one that sets `struct_value_syms`) now
has an `Isolated(Named(...))` arm, so an iso-wrapped struct param DOES reach
`struct_value_syms` registration — the precondition this doc's item #4
documented as permanently unreachable now holds. The downstream
`mir_lowering_stmts.spl` TODO fix (route iso-typed struct place-reads through
`emit_move` instead of `maybe_copy_struct_value`) has been implemented and is
spec-covered (`iso_move_pipeline_spec.spl`, extended with a struct-typed iso
binding case, 4/4, sabotage-verified: `4 total, 3 passed, 1 failed` →
reverted `4/4`, independently re-verified). Items #1-3 below are still open.

## Background

`HirTypeKind.Isolated` survives HIR and the NLL borrow checker
(`src/compiler/55.borrow/borrow_check/borrow_graph.spl`) has real, spec-proven
`Move` handling (`record_move`, forward-propagated via `moved_now`). Before
this lane, `MirBuilder.emit_move` (`src/compiler/50.mir/mir_data.spl:353`) had
exactly ONE caller in the whole compiler: the variable-to-variable let-binding
site (`src/compiler/50.mir/mir_lowering_stmts.spl:743`-ish, guarded by
`mir_hir_type_is_isolated`, `mir_lowering_stmts.spl:48`). Every other way an
iso value transfers ownership emitted a plain Copy (or, for several sites, no
copy/move INSTRUCTION at all -- just an operand reference), starving the
borrow checker of Move facts.

## What this lane did

Closed the **function-call-argument** gap: an iso-typed argument passed to a
function whose DECLARED parameter type is also `iso` now gets a synthetic
`emit_move(fresh_local, arg_local)` ahead of the call
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, the
`declared_param_type.kind` match inside `lower_call`'s direct-call argument
loop, new `case HirTypeKind.Isolated(_):` arm). Proven by
`test/01_unit/compiler/borrow/iso_move_sites_spec.spl` (hand-built HIR, same
technique as `iso_move_pipeline_spec.spl` -- the parser cannot yet parse
`iso T` in parameter position, see
`doc/08_tracking/bug/iso_mut_capability_prefix_not_parsed_2026-07-29.md`).
Sabotage-verified: swapping the new `emit_move` for `emit_copy` turned the
spec's positive case red (2 passed -> 1 passed, 1 failed); reverting restored
green (2/2).

**Known limitations of the call-argument fix itself** (not separately filed,
scoped here):
- Only fires when the CALLEE's declared parameter type is `iso` (the
  argument's own source type is not what's checked) -- `call_param_types` is
  recovered from `resolved_call_hir_param_types` or the name-keyed
  `bootstrap_fn_param_hir_types_lookup` registry, which real driver runs
  populate via `prescan_module_struct_names`
  (`src/compiler/80.driver/driver_pipeline_lowering.spl:213,264`) but a
  hand-built single-module test must call explicitly.
- Direct-call arguments only. The indirect paths in the same function --
  `arg_operands.push` at `switch_operators_calls.spl:4104` (a resolved
  named-function-value operand) and `:4116` (a lowered lambda value) -- bypass
  the new branch entirely and remain open gaps.

## Open gaps (not attempted this lane; each needs a dedicated Move-emission +
checker-arm fix, not attempted speculatively per this lane's scope of "one
correct site")

### 1. Returning an iso value -- DOUBLE gap (lowering AND checker) — CLOSED 2026-08-07 (WP-F, see update at top of doc)
- **Lowering:** no function in `src/compiler/50.mir/_MirLowering/**` or
  `_MirLoweringExpr/**` emits a Move ahead of a `Ret` terminator for an
  iso-typed tail/return expression; the terminator carries a bare operand.
  `iso_move_pipeline_spec.spl:170-174`'s own comment already states this: "a
  bare trailing `a` read ... the checker's terminator conversion does not see
  at all -- `MirTerminator.Ret(_)` drops its operand, a pre-existing,
  separate blind spot left as-is".
- **Checker:** `src/compiler/55.borrow/borrow_check/mod.spl`'s
  `analyze_instruction` (lines ~159-199) has match arms for `Ref`, `Copy`,
  `Move`, `Const` only, with a `case _: pass_do_nothing` catch-all --  there is
  no terminator-walking arm at all in this function, and the sibling
  `convert_terminator` (~line 142) builds a `Terminator.Call`/`Unreachable`
  shape that discards operands. Even if lowering emitted a Move ahead of
  `Ret`, the checker's terminator-side plumbing would still need work to
  observe it. Fixing lowering alone would be silently inert -- this is why
  this lane picked the call-argument site instead, where both lowering AND an
  existing `Move`-consuming checker arm (`Copy`/`Move` cases above) were
  already wired.

### 2. Assigning an iso value to an already-existing variable (not a fresh `val`) — CLOSED (commit `6a53442fbd1`, `test/01_unit/compiler/borrow/iso_move_assign_field_spec.spl`, 8/8)
- `src/compiler/50.mir/mir_lowering_stmts.spl:1039`:
  `b.emit_copy(local, assigned_value)` inside the plain-assignment
  (`op == nil`) arm of the `Assign` statement lowering (`Var`/`NamedVar`
  target case, around line 1005-1044). Always Copy, regardless of whether
  `assigned_value`'s HIR type is `Isolated`. This file is explicitly fenced
  out of this lane's edit scope (`src/compiler/50.mir/_MirLowering/**` and
  `_MirLoweringExpr/**` only, `mir_lowering_stmts.spl` off-limits -- another
  agent was editing it concurrently), so citing file:line only, not fixing.

### 3. Storing an iso value into a struct field — CLOSED (commit `6a53442fbd1`, same spec, 8/8; array/dict element-store follow-up below also closed by the same commit)
- `src/compiler/50.mir/mir_lowering_stmts.spl:1147`:
  `b.emit_set_field(mir_operand_copy(receiver), field_index,
  mir_operand_copy(assigned_field_value))` inside the `Field(base, field,
  resolved)` assignment-target arm (starts ~line 1093). Same shape as the
  call-argument gap THIS lane closed: `emit_set_field` takes bare
  `MirOperand` references, not a Copy/Move instruction, so there is nothing
  for a Move to "replace" -- a fix here needs the same synthetic
  `emit_move(fresh, assigned_field_value)`-ahead-of-store pattern this lane
  used for call arguments. The borrow checker's `analyze_instruction`
  (`borrow_check/mod.spl`) also has no `SetField`/aggregate-store arm, so
  even a lowering-side fix alone would need a matching checker arm (same
  double-gap shape as the return site above) -- not confirmed whether one is
  needed since `SetField` was not investigated on the checker side in this
  lane; flag for whoever picks this up.
- Array-element store was not separately located in this lane's grep sweep
  (`grep -rn "MirInstKind.Store\|emit_store\|SetField\|StoreField\|StoreIndex"`
  across `_MirLoweringExpr/**` and `_MirLowering/**` turned up only
  `StoreGlobal` (module-level constants, `module_lowering.spl:1278`, not a
  candidate transfer site) and `emit_store` used for short-circuit
  logical-operator result slots (`expr_dispatch.spl:2320,2335`, not
  array-element storage) -- the real array-element write path was not
  identified; needs its own audit pass before a fix can be scoped.

### 4. `mir_lowering_stmts.spl:664` struct-binding TODO's premise does not hold today (WP-S, 2026-08-07)

`mir_lowering_stmts.spl:664-672` carried a TODO claiming an iso-typed
`struct` (not class) place-read binding (`val b = a` where `a: iso Point`)
takes the `maybe_copy_struct_value` path (`mir_lowering_stmts.spl:217`) and
gets a field-by-field Copy instead of a Move. WP-S was scoped to implement
exactly that TODO, in this file only. The implementation itself was
straightforward (mirror the working precedent at what is now line ~742: gate
on `mir_expr_kind_is_place(let_init.kind) and
mir_hir_type_is_isolated(find_local_hir_type(init_local.id))`, emit_move via
a fresh `new_local` before falling into `maybe_copy_struct_value`), but **the
scenario the TODO describes is currently unreachable from any hand-buildable
HIR shape**, so there is nothing for the new branch to do — every path that
sets `struct_value_syms[local.id]` (making a local struct-registered, the
precondition for the whole `maybe_copy_struct_value` bypass to even be
considered) and every path that sets `find_local_hir_type(local.id)` to
`HirTypeKind.Isolated(_)` (the precondition for the move check) are mutually
exclusive in the current codebase:

- **Parameter binding** (`function_lowering.spl:206-210` vs `:239`): both
  match on the exact same `param.type_.kind` field. Line 206 fires only when
  the kind is `Isolated(_)` (remembers the HIR type via
  `remember_local_hir_type`). Line 239 fires only when the kind is
  `Named(type_symbol, _)` (sets `struct_value_syms`). An `iso Point` param's
  kind is `Isolated(Named(Point,[]))` — the outer tag is `Isolated`, so only
  line 206 fires; `struct_value_syms` is never set for that local. Empirically
  confirmed: a hand-built-HIR probe (`fn take(a: iso Point) -> i64: val b = a;
  val c = a; 0`) reports `errors.len() = 1` **identically before and after**
  applying the WP-S fix (tested via `git apply -R`/`git apply` on the saved
  diff) — the existing non-struct fallback branch
  (`mir_lowering_stmts.spl`, the `new_local`+`emit_copy`/`emit_move` arm) already
  catches this case correctly, precisely because `struct_value_syms` staying
  nil routes it away from `maybe_copy_struct_value` entirely.
- **`lower_struct_construct`** (`switch_operators_calls.spl:3200`): sets
  `struct_value_syms` unconditionally for any struct-literal result, but never
  calls `remember_local_hir_type` — a fresh construction has no source to
  inherit iso-ness from.
- **The non-struct fallback's own forwarding** (`mir_lowering_stmts.spl`,
  the `new_local`+`emit_move`/`emit_copy` arm): forwards
  `found_init_hir_type` onto the new local via `remember_local_hir_type` when
  present (so iso-ness threads through a CHAIN of primitive moves), but never
  writes `struct_value_syms` — so a local that reaches this branch can never
  subsequently satisfy the struct-registered precondition either, closing the
  chain-propagation route.
- **Field-read provenance** (`expr_dispatch.spl:362`
  `remember_field_projection_provenance`): sets `struct_value_syms[result.id]`
  from `struct_field_type_name` (a name observed at a PRIOR construction site,
  not from the field's declared HIR type), and never calls
  `remember_local_hir_type` at all — so `outer.child` for a
  `child: iso Point` field cannot establish Isolated-ness on the projected
  local either, even though the base struct itself might be plain
  (`struct_value_syms`-registered).

**Net effect:** `find_local_hir_type(x) == Some(Isolated(_))` and
`struct_value_syms.get(x) != nil` never hold for the same local `x` anywhere
in the current lowering pipeline. The TODO's fix is real ownership-hole
prevention *once reachable*, but implementing it now would ship an unreachable
branch with no way to write a spec that can go red (violates the "test that
cannot fail proves nothing" bar) — action taken: **reverted the WP-S code
change**, left the TODO in place (not converted to a NOTE — its premise is
what's wrong, not the intent), and filed this finding instead.

**Unblocks when:** `function_lowering.spl:239`'s match is taught to unwrap
`HirTypeKind.Isolated(inner)` before checking `inner.kind` for `Named(...)`
(mirroring what `function_lowering.spl:729`'s `lower_type` already does for
the separate MIR-type-lowering concern) — that single change would let an
`iso Point` param populate `struct_value_syms` *and* keep the existing line-206
`remember_local_hir_type` call, making both preconditions hold simultaneously
and the `mir_lowering_stmts.spl:664` branch (once (re)implemented) reachable
and testable. That file is out of scope for WP-S (fenced to other concurrent
agents); whoever owns it next should re-open this TODO alongside that fix.

## Follow-up audit (2026-08-07, read-only): array/dict element store located

The prior lane's grep sweep (item 3's last bullet, above) said the real
array-element write path "was not identified." It has now been found — it is
NOT under `MirInstKind.Store`/`emit_store`/`StoreIndex` at all, it is a
runtime-call emission, same shape as `.push()`:

- **`arr[i] = value`** — `src/compiler/50.mir/mir_lowering_stmts.spl:1139`,
  `case Index(base, index):` inside `lower_assign`'s statement-target match.
  The value operand is lowered (`value_local`), optionally combined for a
  compound op, then boxed and passed to `rt_array_set` as a bare
  `mir_operand_copy(boxed_value)` (line ~1225: `self.builder.emit_call(func_operand,
  [mir_operand_copy(receiver), mir_operand_copy(index_local),
  mir_operand_copy(boxed_value)], MirType.unit())`). **No `emit_move` anywhere
  in this arm.** An iso value stored here produces a plain Copy operand
  reference, not a MIR `Move` — the borrow checker never sees a transfer fact.
- **`d[k] = v`** — same `Index(base, index)` arm, the earlier `if
  self.local_is_runtime_dict(receiver):` branch (mir_lowering_stmts.spl
  ~line 1139-1170). Value goes through `box_runtime_value(dict_value)` then
  `b_dset.emit_call(dict_set_op, [mir_operand_copy(receiver),
  mir_operand_copy(dict_key), mir_operand_copy(boxed_value)], MirType.i64())`
  — same bare-Copy shape, **also no Move**.
- **`list.push(x)`** — a separate, sibling gap in a different file:
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:874`,
  `me lower_unresolved_array_push(...)`. `Array.push` has no method symbol
  (confirmed at the call site, `method_calls_literals.spl:2459`: "Builtin
  Array.push has no method symbol... lower it immediately"), so it never
  reaches `lower_call`'s direct-call argument loop where this lane's
  `HirTypeKind.Isolated(_)` fix lives
  (`switch_operators_calls.spl:4153`). The pushed value is lowered
  (`push_val_raw = self.lower_expr(push_value)`), boxed, and passed as
  `mir_operand_copy(push_val_tagged)` to `rt_array_push`
  (`method_calls_literals.spl:886`). No Move.
- **`dict.set(k, v)` vs `d[k] = v`** — asymmetry confirmed structurally, not
  just behaviorally: unlike `push`, no `method == "set"` unresolved-builtin
  branch exists anywhere in `_MirLoweringExpr/**`
  (`grep -n 'method == "set"' _MirLoweringExpr/*.spl` → no hits). So `.set()`
  is not intercepted as a builtin the way `push`/bracket-assign are; it falls
  through to `lower_method_call`'s resolved-symbol paths
  (`InstanceMethod`/`FreeFunction`), which — if the callee's declared
  parameter type is recorded as `iso` — CAN reach the same direct-call
  argument loop and its `HirTypeKind.Isolated(_)` Move-emission arm that
  `switch_operators_calls.spl:4153` added for ordinary function calls. This
  was not run to a concrete positive/negative result in this read-only pass
  (would require a resolved `Dict.set` symbol with a declared `iso` parameter
  to probe), but it is the structural mechanism that would explain the
  existing memory note that `.set()` and `d[k] = v` behave differently on
  both engines (`reference_dict_bracket_assign_beats_set_both_engines.md`) —
  worth a dedicated positive/negative probe before assuming either way.

**Net for this follow-up:** three confirmed no-Move transfer sites
(`arr[i]=`, `d[k]=`, `.push()`), all sharing the same fix pattern already
proven for call arguments: lower the value normally, then
`emit_move(fresh, value_local)` immediately before the box/call, and pass
`fresh` instead of `value_local`. All three are runtime-call emission sites
(`rt_array_set`/`rt_dict_set`/`rt_array_push`), not `MirInstKind.Store`
instructions — the original grep for `Store`/`SetIndex`/`StoreField` was
looking for the wrong instruction family; the transfer happens at the
`emit_call` boundary via a boxed argument operand, exactly like the call-arg
site this lane already fixed.

## Evidence trail
- `test/01_unit/compiler/borrow/iso_move_sites_spec.spl` -- the closed gap's
  proof (2/2 passed) + sabotage probe (2/2 -> 1/2 with `emit_move` swapped for
  `emit_copy`, reverted to restore 2/2).
- `test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl` -- prior lane's
  let-binding proof + the terminator/return blind-spot comment cited above.
- `src/compiler/50.mir/mir_data.spl:353-369` -- `emit_move`'s own docstring,
  the original "no caller yet" audit this lane's audit continues.
