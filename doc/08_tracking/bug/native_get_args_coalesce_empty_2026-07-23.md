# native (entry-closure): get_args() always [] — `?? []` on non-optional extern result emits rt_is_some on a raw SplArray*

- **Date:** 2026-07-23  **Status:** OPEN (diagnosed by disasm, W81 + rLSP3)
- **Severity:** high — argv is empty in every entry-closure native
  (`--version`/`--help`/flag parsing dead; stdio servers unaffected in serve
  loops).

## Evidence (objdump of lib.nogc_sync_mut.io_runtime.get_args, rLSP3)
```
call rt_get_args        ; returns RAW SplArray* (untagged)
call rt_is_some         ; raw ptr fails the Some check
je   -> rt_array_new(0) ; always takes the [] arm
sar  $0x3,%rax          ; untag shift applied to the fresh array
```
Source: `pub fn get_args() -> [text]: sys_get_args() ?? []` where
`extern fn sys_get_args() -> [text]` (NON-optional). The `??` should be
an identity on a non-optional operand but codegen emits an rt_is_some
discrimination against the raw pointer, which never passes.

Note: the emitted call goes to rt_get_args (extern alias of sys_get_args in
the native lane); a C `sys_get_args` bridge was also added to
runtime_native.c (harmless, currently unreferenced).

## Also suspicious
The taken arm applies `sar $3` (untag) to rt_array_new's result while the
extern arm would return rt_get_args' raw pointer unshifted — the two arms
disagree on tagging; audit extern `-> [T]` return-tag conventions.

## Fix direction
- MIR lowering: `x ?? d` where x's declared type is non-optional must be a
  no-op (pass through), never an rt_is_some probe.
- Audit tag convention for extern functions returning arrays (raw SplArray*
  vs <<3 handle) at call sites.

## Repro
W81: entry `val a = get_args(); print a.len()` with extra CLI args → prints 0.


## 2026-08-17 CORE-P1 triage: STILL PRESENT in current source

Re-verified against CURRENT SOURCE during the crit_01 CORE-P1 sweep. Confirmed still present, and now located precisely on both sides. PRODUCER: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1285-1286` types get_args as a BARE array, never an Option -- `if name == "get_args" or name == "get_cli_args": return MirType.ptr(self.bootstrap_text_array_type(), false)`. CONSUMER: `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:3518-3575` `case NullCoalesce(left, right):` emits `MirConstValue.Str("rt_is_some")` on `left_local` UNCONDITIONALLY, with no guard that `left` is Option-typed. So `get_args() ?? []` hands a raw `SplArray*` to `rt_is_some`, which reads a tag out of a heap pointer.\n\nSuggested shape of the fix (NOT implemented -- see caveat below): in the `NullCoalesce` arm, when the left operand is POSITIVELY typed as a non-nullable collection (`HirTypeKind.Array`/`Slice`/`Dict`), the coalesce is statically the left operand, so yield `left_local` and skip the `rt_is_some` branch entirely. The guard must require a positively-known non-Optional type, NOT merely `hir_expr_is_optional_type(left) == false` -- that helper (expr_dispatch.spl:102-110) also returns false for an expression with NO recorded type, and the file itself documents a "raw migration form" where a genuine Option carries no `local_hir_types` entry. Using the loose test would silently break those.\n\nCAVEAT -- this fix was NOT landed and is NOT verified. Reproduction requires `native-build --entry-closure`, which was attempted and TIMED OUT at 7 minutes on a host at load average 302; no before/after Results line was obtained, so the fix above is a located hypothesis, not a proven one.

## 2026-08-17 CRIT-C4 re-confirmation (SOURCE READING; execution blocked)

Both halves of the prior crit_01 localization still hold verbatim in current
source. PRODUCER `switch_operators_calls.spl:1285-1286` still returns a bare
`MirType.ptr(bootstrap_text_array_type(), false)` for `get_args`/`get_cli_args`.
CONSUMER `expr_dispatch.spl:3518` `case NullCoalesce(left, right):` still emits
`MirConstValue.Str("rt_is_some")` on `left_local` unconditionally (:3570-3577) —
read the whole arm: it computes `result_struct_name` provenance but never tests
whether `left` is Option-typed at all. Fix NOT landed; native-build verification
still unobtainable (host load 66-90; a native check produced no output in 25 min).

Note for whoever lands it: on the HOST engines this same `??` arm is ALSO wrong in
the Some direction — `(ret_some(42) ?? 0) == 42` is `true` interpreted and `false`
on the JIT (rc=0 both). So `??` has a payload-representation defect independent of
the non-Optional-left guard proposed here. See the 2026-08-17 CRIT-C4 note in
native_inlined_option_return_representation_mismatch_2026-08-02.md.
