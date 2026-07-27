# Root cause: native `.get()` on nil Dict receiver returns phantom Some; `.len()` returns -1

**Date:** 2026-07-27
**Status:** Root-caused (analysis only — no src/ change in this lane)
**Parent bug:** `doc/08_tracking/bug/hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`
**Red spec:** `test/01_unit/compiler/hir/nil_dict_receiver_phantom_option_spec.spl`

## TL;DR

The C runtime is already fail-closed: `rt_dict_get` on a nil/invalid receiver
returns the tagged nil sentinel `3`. The defect is in MIR lowering's
**`decode_runtime_value`** (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:482-572`),
which re-interprets that result by the dict's static value type *before any nil
check can see it*: the integer arm computes `raw >> 3`, mapping the nil
sentinel `3 -> 0`. Since native `nil` compares against `3`
(`expr_dispatch.spl:1480-1513`), the decoded `0` passes `!= nil` — a phantom
`Some(0)`. `.len()` results are never decoded, so its in-band soft sentinels
(`0` or `-1`) survive — hence the divergence.

## Mechanism — exact chain

Runtime value encoding (`src/runtime/runtime_native.c:93-100`):
`TAG_MASK=0x7`, `TAG_INT=0x0`, `TAG_HEAP=0x1`, `TAG_SPECIAL=0x3`;
`nil = (NIL_payload<<3)|TAG_SPECIAL = 3` (`runtime_native.c:1311-1317`).
Native `nil` literal is materialized as constant `3`
(`expr_dispatch.spl:1511-1513`, rationale comment 1480-1510), so every
`x != nil` compiles to `x != 3` (inttoptr'd for pointer compares).

### `.get(key)` path

1. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1244-1262`
   — `.get` lowers to a call of `rt_dict_get(receiver, key)` and then
   **`return self.decode_runtime_value(get_local2, get_value_type)`**
   (line 1261), where `get_value_type` is the dict's static value MIR type.
2. `src/runtime/runtime_native.c:4779-4781` — `rt_dict_get` =
   `rt_core_dict_lookup(rt_core_as_dict(dict), key)`.
   `rt_core_as_dict(3)` fails the `TAG_HEAP` check (`runtime_native.c:1118`)
   → `NULL`; `rt_core_dict_lookup(NULL,...)` returns `rt_core_nil()` = **3**
   (`runtime_native.c:4707-4708`). Runtime behavior is CORRECT and
   fail-closed. (Receiver nil-filled as `0` behaves identically: tag `0` is
   not `TAG_HEAP` → same path.)
3. `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:486-491` — the
   **integer arm** of `decode_runtime_value` emits `raw >> 3`:
   `3 >> 3 = 0`. The out-of-band nil sentinel is destroyed and becomes the
   in-band integer `0`.
4. Consumer check `got != nil` → `0 != 3` → **true** → phantom `Some(0)`.
   In the stage-4 crash, the phantom `0` is a decl *index* (the six
   `register_imported_symbol` lookups are `Dict<text, i64>`-shaped); the
   trait arm then indexes another nil-filled collection with it → segfault.
5. String-valued dicts have the same hole via a different arm:
   `expr_dispatch.spl:549-569` calls `rt_interp_cstr(raw)`;
   `rt_interp_cstr(3)` returns `NULL` (`runtime_native.c:1872-1876`,
   `v < 0x10000` guard) → phantom non-nil `Some(NULL char*)` (`0 != 3`),
   segfault on first use.
6. Struct/erased value types fall to the default arm
   (`expr_dispatch.spl:570-572`) which returns raw `3` unchanged — those
   compare `3 == nil` correctly. The corruption is specific to arms that
   TRANSFORM the raw value (integer Shr, string cstr).

### Why `.len()` returns -1 (and diverges)

`.len()` results are returned as raw i64 — **never passed through
`decode_runtime_value`** (`method_calls_literals.spl:1361-1379`). Two routes:

- Statically-typed Dict receiver → `rt_dict_len`
  (`method_calls_literals.spl:2500,2516`): `rt_dict_len(3)` →
  `rt_core_as_dict` NULL → returns **0** (`runtime_native.c:4825-4828`).
- Untyped/erased receiver (the compiler's actual route — Module values come
  out of `modules_by_name.get()` erased, so the `.functions` field-load local
  has no visible dict-ness): `resolution == Unresolved` → `rt_len` fallback,
  rewritten to `rt_string_len` when the local is not a known runtime array
  (`method_calls_literals.spl:1355-1369`). `rt_string_len(3)`: not a
  registered string and `3 < 0x10000` → returns **-1**
  (`runtime_native.c:1741-1745`). This is the `-1` the landed
  `functions.len() < 0` mitigation guards key on.

So: len fails **soft, in-band** (`0`/`-1`, no decode); get fails because the
decode step destroys the **out-of-band** sentinel. The interpreter fails loud
("method `get` not found on type `nil`") because it dispatches on the value
tag before any method table lookup.

## Proposed minimal fix (NOT applied — proposal only)

Make the integer arm of `decode_runtime_value` nil-preserving:
`decoded = (raw == 3) ? 3 : (raw >> 3)`. One site fixes `.get`, `d[k]`
indexing, and `.keys()`/`.values()` element decode simultaneously. Branch-free
select (Eq/Mul/Add) avoids needing a MIR select instruction or new blocks.

**No false positive is possible:** boxed ints carry `TAG_INT=0` (low 3 bits
`000`, a stored 3 is raw `24`), heap handles carry `001`, floats `010` — raw
`3` can only ever be the nil sentinel. (Tagged `true`=11, `false`=19.)

```diff
--- a/src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl
+++ b/src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl
@@ -486,9 +486,25 @@
         if is_integer:
+            # Nil-preserving decode (bug native_nil_dict_get_phantom_option):
+            # rt_dict_get / rt_array element reads return the tagged nil
+            # sentinel (3 = SPECIAL|NIL) for a nil/invalid receiver or missing
+            # key. A bare Shr-by-3 maps 3 -> 0, forging a phantom Some(0) that
+            # passes `!= nil` (NilLit materializes nil as 3). Select the
+            # sentinel through unchanged: decoded = raw==3 ? 3 : raw>>3.
+            # Unambiguous: boxed ints carry TAG_INT=0 in the low 3 bits, so a
+            # raw value of exactly 3 can never be data.
             val shift = b.emit_const_int(3)
             val value = b.emit_binop(MirBinOp.Shr, mir_operand_copy(raw), mir_operand_copy(shift), MirType.i64())
-            val decoded = b.emit_cast(mir_operand_copy(value), result_type)
+            val nil_const = b.emit_const_int(3)
+            val is_nil_b = b.emit_binop(MirBinOp.Eq, mir_operand_copy(raw), mir_operand_copy(nil_const), MirType.bool())
+            val is_nil = b.emit_cast(mir_operand_copy(is_nil_b), MirType.i64())
+            val one = b.emit_const_int(1)
+            val not_nil = b.emit_binop(MirBinOp.Sub, mir_operand_copy(one), mir_operand_copy(is_nil), MirType.i64())
+            val keep_nil = b.emit_binop(MirBinOp.Mul, mir_operand_copy(is_nil), mir_operand_copy(nil_const), MirType.i64())
+            val keep_val = b.emit_binop(MirBinOp.Mul, mir_operand_copy(not_nil), mir_operand_copy(value), MirType.i64())
+            val merged = b.emit_binop(MirBinOp.Add, mir_operand_copy(keep_nil), mir_operand_copy(keep_val), MirType.i64())
+            val decoded = b.emit_cast(mir_operand_copy(merged), result_type)
             self.builder = b
             return decoded
```

Follow-up (same family, separate change): guard the string arm the same way —
select raw `3` through instead of `rt_interp_cstr(3)`'s NULL
(`expr_dispatch.spl:549-569`).

**Do NOT "fix" `rt_string_len`'s `-1`** (`runtime_native.c:1744`) as part of
this: the landed stage-4 mitigations in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` key on
`functions.len() < 0`; changing `-1` to `0` before those guards are relaxed to
`<= 0` would silently disarm them.

## Risk assessment — who else rides this decode

`decode_runtime_value` integer-arm callers (all get the fix, all benefit):
- `.get(key)` (`method_calls_literals.spl:1261`) — the crash path.
- `d[k]` Index reads (`expr_dispatch.spl`, the path `.get` was documented to
  mirror; its "garbage-on-miss" item 15 in scratchpad/dict_native_report.md is
  the same sentinel destruction — a real key MISS on a *valid* dict also
  returns 3 and currently decodes to 0).
- `for k in d.keys() / .values()` element decode; array element reads.

Behavior deltas to expect: code that (incorrectly) relied on a missing key
reading as `0` via `d[k]` will now see nil (3). Under the documented
payload-3 collision (`native_i64opt_some0_collapses_to_nil_2026-07-14.md`,
`reference_jit_option_i64_value3_none_collision`), a genuinely stored `i64`
value `3` already reads as nil-equal after decode — this patch does not widen
that pre-existing, accepted collision. Perf cost: 6 extra ALU ops per decoded
integer element read; no calls, no branches.

## How the red spec validates the fix

`test/01_unit/compiler/hir/nil_dict_receiver_phantom_option_spec.spl`
(deliberately red, native):
- it 1: `StubModule` with omitted `imported_const_decls: Dict<text,i64>` →
  `.get("k")` raw = 3 → with the patch, decode preserves 3 →
  `expect(got).to_be_nil()` passes (today: decodes 0 → red).
- it 2: `.len()` on the statically-typed field → `rt_dict_len` → 0 → takes the
  `n <= 0` branch → `expect(got).to_be_nil()` passes with the patch. If a
  future len route yields -1 (rt_string_len fallback), the same branch covers
  it — the spec pins the agreement contract, not a specific sentinel.
Run: `bin/simple test test/01_unit/compiler/hir/nil_dict_receiver_phantom_option_spec.spl`
(native lane; the "Results:" line is authoritative). Once green, the two
`functions.len() < 0` mitigation guards in `module_lowering.spl` become
defense-in-depth and can be relaxed on their own schedule.
