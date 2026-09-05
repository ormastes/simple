# Tuple constant index out of range reads out-of-bounds with no diagnostic

- **ID:** tuple_constant_index_out_of_range_reads_oob_no_diagnostic_2026-08-08
- **Date:** 2026-08-08
- **Status:** FIXED (MIR-level) — `t.5` on a 2-element tuple now fails
  `native-build` with `error: MIR lowering error: tuple index 5 is out of
  range for a 2-element tuple`, rc=1. Valid indices (`t.0`, `t.1`,
  `t.0 + t.1`, whole-tuple `{t}` interpolation, mixed-type tuples) are
  unaffected. Fenced by `scripts/check/check-tuple-index-out-of-range.shs`.
- **Severity (pre-fix):** medium — out-of-bounds heap read, but the index is
  a compile-time constant, so it is not runtime-attacker-controlled. Exit 0
  with no diagnostic was indefensible when arity is statically known.

## Symptom (pre-fix)

```
fn main() -> i64:
    val t = (7, 9)
    print("oob: {t.5}\n")
    return 0
```

```
$ env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build \
    --source <dir> --entry-closure --entry <dir>/main.spl --cache-dir <tmp>/c --output <tmp>/b
build_rc=0            # no error, no warning
$ <tmp>/b
oob: 0
```

Index 5 on a 2-element tuple. A tuple is a raw `rt_alloc(field_count*8)` block
— 16 bytes here — so `t.5` reads at offset 40, **24 bytes past the end**.
Reproduces identically without string interpolation (`val x = t.5` → `x=0`), so
it is not an interpolation artifact.

## Why nothing caught it (pre-fix)

`emit_bounds_check_for_index` (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`,
~line 1293) takes its bailout branch for a tuple base — a tuple has no length
symbol and is not a runtime array — and `return`s without emitting the
`bounds_check` intrinsic. Every MIR consumer therefore inherited the hole by
construction; it was not a Cranelift- or LLVM-specific defect. This part of
the bailout machinery is UNCHANGED by this fix — tuple bases still take the
bailout return for the general bounds-check intrinsic (a tuple genuinely has
no runtime length symbol to check against). What changed is that an
OUT-OF-RANGE literal index on a tuple is now caught earlier, as a distinct
compile-time-constant check, before that bailout is ever relevant.

## Fix landed 2026-08-08

Landed at the MIR level, inside `lower_index_expr`
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`), in the
`case MirTypeKind.Tuple(field_types):` arm (this arm already existed for a
different reason — the 2026-08-07 gap-(c) mixed-type tuple field-read fix,
`tuple_field_mir_types` / `tuple_index_literal`, landed by a parallel session
and NOT modified by this fix beyond adding the check below it):

```
val mir_tuple_lit_idx = self.tuple_index_literal(index)
if mir_tuple_lit_idx >= 0 and mir_tuple_lit_idx >= field_types.len():
    self.error_fatal("tuple index {mir_tuple_lit_idx} is out of range for a {field_types.len()}-element tuple", base.span)
```

Two things had to be right for this to actually abort the build, both
discovered empirically while landing this fix (not obvious from reading the
error-reporting API alone):

1. **`self.error()` alone is non-fatal.** `MirLowering.error()`
   (`src/compiler/50.mir/_MirLowering/asm_and_targets.spl:264`) pushes a
   `MirError(fatal: false)`; whether a non-fatal MIR error aborts the build is
   decided by a *deprecated message-text allowlist* in `80.driver`
   (`_mir_error_is_fatal`). A first attempt using plain `self.error(...)`
   built successfully with **no error printed at all** despite the check's
   condition being true (confirmed by a temporary print marker showing
   `lit_idx=5 n_fields=2` — the comparison fired, but the diagnostic was
   silently swallowed downstream). `self.error_fatal(...)` pushes
   `fatal: true` explicitly and is documented as "the way to guarantee this
   aborts the build" — switching to it made the build fail with rc=1 and the
   expected message.
2. The check must live in the `Tuple(field_types)` match arm added by the
   2026-08-07 gap-(c) session (uncommitted, in-progress at the time this fix
   landed) — that arm is what makes `field_types` (the tuple's own
   MIR-registered field list, no Dict lookup involved) available at this
   call site. `field_types` and `tuple_index_literal(index)` are both
   independent of the HIR-level `local_tuple_types` Dict that the originally
   proposed HIR-level fix relied on (see next section for why that matters).

## HIR-level fix is reachable but currently inert (superseded finding)

The previous version of this doc recorded the fix as unverifiable because
"`bin/simple` resolves to the Rust seed, so the `.spl`-side HIR desugar for
`t.N` is unreachable." **That theory is WRONG and was disproven empirically
on 2026-08-08.** An unconditional marker print placed as the first statement
of `field_tuple_element_type`
(`src/compiler/20.hir/hir_lowering/expressions.spl:182`) DID fire under
`native-build` (`MARKER-HIR-SITE-FIRED field_tuple_element_type index=5`),
proving `.spl` HIR-lowering edits are live on this path. A sibling marker in
`emit_bounds_check_for_index` (the MIR site) also fired
(`MARKER-MIR-SITE-FIRED emit_bounds_check_for_index base_local=4`) in the
same build. Both `.spl` sites are live.

However, implementing the HIR-level fix as originally specified — a
`field_tuple_arity` helper mirroring `field_tuple_element_type`'s
`rt_dict_contains(self.local_tuple_types, base_symbol.id)` lookup, called
from the `is_tuple_positional_field` branch around
`expressions.spl:606-620` — did NOT fire the error for `t.5`, even though the
call site itself was reached (confirmed by a debug print immediately before
the check: `MARKER-ARITY-CHECK idx=5 arity=-1 base_sym_id=1
base_sym_valid=true`). The symbol id matched exactly between registration
(`MARKER-REGISTER-TUPLE sym_id=1 n_elems=2`, from
`try_register_local_tuple_type` in `statements.spl:82`, which unconditionally
fires for `val t = (7, 9)`) and lookup — same `sym_id=1`, same scope — yet
`rt_dict_contains(self.local_tuple_types, base_symbol.id)` returned `false`
**immediately after** the insert (`self.local_tuple_types[sym.id] =
elem_types; rt_dict_contains(self.local_tuple_types, sym.id) → false`,
verified with a debug print placed directly after the assignment). This is
the SAME family as the already-documented native `Dict.get()`/`.len()`
corruption pitfalls (`doc/07_guide/language/dict_native_pitfalls.md`), not a
reachability problem: `HirLocalTupleTypes = {i64: [HirType]}` is a
value-typed dict field on a `class HirLowering` (reference semantics at the
class level, but the dict read-after-write is still corrupt under
`native-build`'s execution of the compiler). The HIR-level fix is therefore
implemented in principle but effectively a no-op today; it was NOT shipped as
the load-bearing fix because it could not be verified to fire (per the "if
the fix cannot be verified to fire, do not ship it" rule) — it was reverted
back out during landing, and the MIR-level fix above is the one actually
shipping. Re-attempt the HIR-level fix once the underlying Dict
read-after-write bug is root-caused; until then any HIR-level tuple-arity
check keyed off `local_tuple_types` should be treated as unverified.

## Regression coverage

`sh scripts/check/check-tuple-index-out-of-range.shs` — new fence, drives two
`native-build` fixtures under `test/fixtures/tuple_index_out_of_range/`:
`bad/main.spl` (`t.5`, must fail with the exact diagnostic) and
`good/main.spl` (`t.0`, `t.1`, `t.0 + t.1`, whole-tuple `{t}` interpolation,
must build and run with the expected output). Sabotage-verified: disabling
the check's condition (`if false and ...`) makes the fence FAIL as expected;
restoring from a pre-sabotage backup and diffing confirmed byte-identical
restoration, then the fence re-PASSed.

`sh scripts/check/check-native-tuple-to-text.shs` still PASSes (unaffected by
this fix); the mixed-type tuple rendering gap it reports (`KNOWN-OPEN —
mixed-type tuple still wrong`) is a separate, pre-existing, already-tracked
issue unrelated to index-range checking.

## Scope caveat (unchanged from original finding)

`local_tuple_types` (and therefore any tracking keyed off it, HIR- or
MIR-side reasoning that consults it) is populated only for
`val t = (literal, literal, ...)` — a tuple whose literal shape is visible at
the `val`/`var` statement. The MIR-level fix that shipped does NOT depend on
`local_tuple_types`; it depends on the tuple's own MIR-registered
`field_types` (populated by `lower_tuple_lit`), which has the same "literal
tuple" scope in practice (a non-literal-init tuple has no field-count-known
type to check arity against in the first place) but through an independent,
verified-working path.

## Note on a `scripts/check/check-aot-lane-fences.shs` roster

The task that produced this fix was asked to add the new fence's basename to
a `FENCES` roster in `scripts/check/check-aot-lane-fences.shs`. That file
does not exist in this repository (confirmed by search); a comment elsewhere
(`doc/08_tracking/bug/paren_less_accessor_whole_module_de_jit_2026-08-08.md`)
references it as if it existed. No such roster was created or modified as
part of this fix — flagging the discrepancy here rather than fabricating a
new aggregator script outside this bug's scope.
