# Lane JITCA — compound assignment drops the load side

**Date:** 2026-07-27
**Status:** fix landed in source; **correct-by-construction, verification blocked on redeploy**
**Bug:** `jit_struct_field_compound_assign_loads_zero_2026-07-27`
(the referenced `doc/08_tracking/bug/` file did not exist in the working tree
when this lane ran — the defect was reproduced directly instead, see Baseline)

## Root cause — exact site

`src/compiler/50.mir/mir_lowering_stmts.spl`, `MirLowering.lower_assign`.

Pre-fix line numbers:

- `case Field(base, field, resolved)` — line **941**
- `case Index(base, index)` — line **967**

Both arms take `op: HirAssignOp?` as a parameter and **never read it**. They
lowered `obj.f <op>= v` / `arr[i] <op>= v` to exactly the same MIR as the plain
`=` form: `emit_set_field(receiver, field_index, value_local)` (line 964) and
`emit_call(rt_array_set, [receiver, index_local, boxed_value])` (line 1001),
where `value_local` is the lowered RHS and nothing else.

So there was no load at all. The store worked; the field's current value simply
never entered the computation, which is observationally `0 <op> rhs`:

| expr (n starts at 5) | pre-fix `bin/simple run` | expected |
|---|---|---|
| `s.n += 2`                       | 2  | 7  |
| `c.mid.inner.n += 4` then `+= 3` | 3  | 7  |
| `arr[1] += 10` on `[1,2,3]`      | 10 | 12 |
| `t.n = t.n + 2` (control)        | 7  | 7  |

This is **not** a depth/place-chain problem — one hop was already wrong. The
sibling arm `lower_assign_var` (lines 789-923) *does* handle `op` correctly, in
both its module-global branch (LoadGlobal / binop / StoreGlobal, lines 829-844)
and its local branch (lines 859-868). Only the two lvalue-projection arms were
missing the read. `lower_assign_op` (HirAssignOp -> MirBinOp) already existed
and was reachable only from `lower_assign_var`.

## Fix shape

`src/compiler/50.mir/mir_lowering_stmts.spl` only. No backend change was needed:
`MirInstKind.GetField` / `rt_array_get` / `rt_dict_get` all already lower
correctly — the MIR simply never contained them for a compound assign.

Three new `impl MirLowering` methods, placed just above `lower_assign_op`:

- `lower_compound_combine(current, op, rhs, type_) -> LocalId` — the single
  read-modify-write core. Callers must pass a `current` loaded from the same
  place they are about to store to; keeping the combine in one helper is what
  makes "one place, one resolution" checkable.
- `compound_field_mir_type(base, receiver, field_index, value_local)` — read-side
  type, preferring the owner struct's declared field type (`struct_field_hir_type`,
  the same table the store side already consults for the Optional-handle
  fix-up), falling back to the RHS local's MIR type, then i64. Stops an f64
  field being read back through the i64 default.
- `compound_elem_mir_type(base, receiver, value_local)` — element type for
  `container[k]`, mirroring the getter's resolution order in expr_dispatch's
  `case Index`: store-observed `runtime_elem_value_type` first (an empty
  `[]`/`{}` literal pins the declared type at i64 and would decode a heap-boxed
  f64 as an integer), then the container's MIR Array/Slice/Dict type, then its
  HIR type, then the RHS type, then i64.

Arm changes:

- **Field.** `receiver` is still lowered exactly once and `field_index` resolved
  exactly once; the compound read is an `emit_get_field(receiver, field_index)`
  using those same two values, then `lower_compound_combine`, then the unchanged
  store. Bitfield targets are detected with the *pure* predicate pair
  `bitfield_type_sym_for(...) >= 0 and bitfield_map.contains(...)` — identical to
  `try_lower_bitfield_set`'s own early-return guard, and it emits no MIR — so the
  packed case reads through `try_lower_bitfield_get` instead of a raw GetField on
  a packed word. The Optional-handle branch now wraps `rhs_value`, not the raw
  `value_local`.
- **Index, dict.** `lower_dict_key(index)` is called once and the resulting key
  local feeds both `rt_dict_get` and `rt_dict_set`. `decode_runtime_value` on the
  read is the exact inverse of `box_runtime_value` on the write.
- **Index, array.** `index_local` is lowered once (before the bounds check) and
  reused by both `rt_array_get` and `rt_array_set`. Read decodes, write boxes.

**Side effects run once** in every arm: no subexpression (`base`, `index`, the
dict key) is lowered more than once — the compound read reuses the already-
lowered local rather than re-lowering the HIR.

**Array value semantics unchanged**: only the READ of the element was added. The
write is the same `rt_array_set` call as before, no aliasing or buffer sharing
was introduced, and no copy was removed.

## Regression spec

`test/01_unit/compiler/compound_assign_place_spec.spl` — 17 `it` blocks, all
with ABSOLUTE expected values (never a comparison against a re-derived
expression, which a lowering that drops the load could satisfy from both sides):

- one-hop field: `+= -= *= /=` (7, 6, 42, 21) and accumulation (0 -> 4 -> 7)
- two-hop `m.inner.n += 2` -> 7
- three-hop `c.mid.inner.n` from 0 (-> 7) and from 5 (-> 7)
- array element `arr[1] += 10` -> 12, neighbours unchanged (1, 3), accumulation,
  and `-=`
- side-effect/place guard: `arr[i] += 10` with `i` a var, asserting all three
  slots (1, 12, 3)
- explicit-form controls: `t.n = t.n + 2`, `c.mid.inner.n = c.mid.inner.n + 2`,
  `arr[1] = arr[1] + 10`, and a plain local `n += 2`

## Verification reached — and its honest ceiling

Editing `src/compiler/**` changes **no** existing binary: `bin/simple` is the
Rust seed and `build/native_probe/simple` embeds a Jul-23 compiler. Nothing
available in this lane executes the edited pure-Simple lowering. `bin/simple
build bootstrap` is forbidden by the standing memory rule (stage4 has ballooned
to ~65GB and been SIGTERM'd), so the fix ships as
**correct-by-construction, verification blocked on redeploy**.

What WAS established:

1. **Baseline reproduced** (`build/jitca_probe.spl`, `bin/simple run`):
   `nested_compound=3`, `array_compound=10`, `onehop_compound=2`.
2. **Expected values confirmed on the interpreter** for the forms it supports
   (`build/jitca_onehop.spl`, `SIMPLE_EXECUTION_MODE=interpreter`):
   one-hop `s.n += 2` -> 7, explicit `t.n = t.n + 2` -> 7, local `k += 2` -> 7.
   The interpreter rejects `c.mid.inner.n += 4` and `arr[i] += v` outright
   ("invalid assignment: deeply nested augmented field access requires
   intermediate variables"), so those forms cannot be cross-checked there.
3. **The spec parses and discriminates** — `bin/simple test
   test/01_unit/compiler/compound_assign_place_spec.spl` -> 17 total, 9 passed,
   8 failed against the unfixed seed (`build/jitca_spec_run.txt`). Crucially
   `arr[1] += 10` FAILS while its explicit control `arr[1] = arr[1] + 10`
   PASSES — that pair isolates the dropped compound read exactly. The two
   three-hop compound failures come with their own explicit control
   `c.mid.inner.n = c.mid.inner.n + 2` also failing, so those belong to the
   separate three-hop place-chain defect, not to this one.
   (Note the known landmine: `bin/simple test` uses a different evaluator than
   `bin/simple run` — one-hop passes under `test` but printed 2 under `run`.)
4. **The edited module parses and loads under the seed frontend** — the
   strongest tier reachable without redeploy. `build/jitca_parsecheck.spl` is a
   3-line driver whose only body is `use compiler.mir.mir_lowering_stmts.*`;
   `bin/simple run build/jitca_parsecheck.spl` returned **rc=0** and printed
   `parsed` (`build/jitca_parsecheck.txt`). The seed therefore lexed, parsed and
   import-resolved the edited file end to end. Zero `E1xxx`, zero parse errors,
   zero unexpected-token. The 1374 `info: Common mistake detected` lines are the
   pre-existing `self.`-is-implicit style notice, emitted across the whole file
   (and the whole tree), not diagnostics on the new code.
   Caveat stated plainly: this proves syntax + imports, NOT that the new
   `emit_get_field` / `rt_array_get` MIR is semantically right at runtime — the
   seed resolves method bodies lazily. The three new helpers' callees
   (`emit_get_field`, `emit_binop`, `local_mir_type_of`, `lower_type`,
   `resolve_base_struct_name`, `bitfield_type_sym_for`, `try_lower_bitfield_get`,
   `decode_runtime_value`, `box_runtime_value`) were each confirmed by grep to
   exist with matching signatures on `MirLowering`.
5. **Parse/E1xxx clean** on both changed files. `bin/simple lint` and
   `bin/simple check` each exceed their timeout while walking the stdlib
   (pre-existing tooling slowness, unrelated to these files) but emitted 0
   errors before being cut — logs in `build/jitca_lint.txt`,
   `build/jitca_check.txt`. `bin/simple fix --dry-run` returned rc=0.

## Post-fix line numbers

`src/compiler/50.mir/mir_lowering_stmts.spl`:
`lower_assign` 925, `case Field` 941, `case Index` 997,
`lower_compound_combine` 1096, `compound_field_mir_type` 1110,
`compound_elem_mir_type` 1138, `lower_assign_op` 1182.

**Not claimed:** that the fixed MIR produces 7 / 7 / 12 on the native path.
That requires the redeploy below.

## Resume command (after redeploy)

```bash
scripts/bootstrap/bootstrap-from-scratch.sh --mode=dynload --deploy
bin/simple run build/jitca_probe.spl        # expect 7 / 12 / 7
bin/simple test test/01_unit/compiler/compound_assign_place_spec.spl
```

Expected after this fix alone: every one-hop, two-hop, array-element and control
case green. The two three-hop compound cases stay red until the separate
three-hop place-chain defect is fixed — their explicit-form control
(`c.mid.inner.n = c.mid.inner.n + 2`) is red today for the same reason.

## Files

- `src/compiler/50.mir/mir_lowering_stmts.spl` — fix
- `test/01_unit/compiler/compound_assign_place_spec.spl` — regression spec
- `build/jitca_probe.spl`, `build/jitca_onehop.spl` — probes (copies; the
  coordinator's originals were not touched)
- `build/jitca_spec_run.txt`, `build/jitca_lint.txt`, `build/jitca_check.txt`,
  `build/jitca_fix.txt` — evidence logs

Not touched: `src/compiler_rust/**` (lane PMR),
`src/compiler/10.frontend/core/interpreter/**` (already fixed), any other
`src/**` call site (lane CAUDIT), the coordinator's probe files.
Nothing committed or pushed.
