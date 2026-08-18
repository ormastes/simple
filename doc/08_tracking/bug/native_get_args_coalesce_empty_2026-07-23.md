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

## 2026-08-18 — fix shape INDEPENDENTLY RE-DERIVED and CONFIRMED; landing DEFERRED (verification structurally unobtainable in this lane)

Re-derived from source without assuming the prior lane's hypothesis, then
compared. **The derivation agrees**, and one extra constraint was found that
is the reason this is not landed blind.

Derivation: `HirTypeKind` (`src/compiler/20.hir/hir_types.spl:915-931`) makes
`Optional(inner)` a distinct variant from `Array(element, size)`,
`Slice(element)`, `Dict(key, value)` and `Tuple(elements)`. An expression whose
HIR type is positively one of those aggregate variants can never hold nil, so
`x ?? d` is *statically* `x`, and any nil-discrimination on it is dead code
that can only take the wrong arm. Reading the whole
`case NullCoalesce(left, right):` arm (`expr_dispatch.spl:3518-3600`) confirms
there is no such test: it computes `result_struct_name` provenance and then
unconditionally builds the `MirConstValue.Str("rt_is_some")` call plus
`then_block`/`else_block`/`merge_block`. Correct guard: yield `left_local`
directly when `left.has_type_` **and** `left.type_.kind` is
`Array`/`Slice`/`Dict`/`Tuple`.

Agreeing with the prior lane: the guard must be **positive**.
`hir_expr_is_optional_type` (`expr_dispatch.spl:103-110`) returns `false` for
an expression with no recorded type, so `not hir_expr_is_optional_type(left)`
would also fire on the documented "raw migration form" where a genuine Option
carries no `local_hir_types` entry, silently breaking it.

**New constraint no prior lane stated:** the guard is a *no-op* unless the HIR
type is actually recorded on the `get_args()` call expression
(`has_type_ == true`). If it is not, the fix compiles, changes nothing, and
would be reported as a fix — precisely the false-green class this campaign
exists to stop. That premise is **unverified**.

**Why verification is structurally unobtainable here, not merely slow.** The
defect is in `src/compiler/50.mir/**`, i.e. pure-Simple *compiler* source.
Unlike `src/lib/**` (read as source every run), compiler source only takes
effect through a **deployed self-hosted binary**. `bin/simple` is currently the
Rust seed (it prints the seed banner), and this lane is forbidden to rebuild or
redeploy `bin/simple` / `bin/release/**` while a bootstrap is running. So no
engine available here executes the edited lowering: `bin/simple test` is the
tree-walk interpreter and `run` is the Cranelift JIT — neither runs `50.mir`
lowering at all, so an interpreted spec cannot exercise this defect however it
is written. The two prior timeouts (7 min at load 302; no output in 25 min at
load 66-90) are symptoms of the same thing: only a full self-hosted
native-build exercises it.

Status: **fix shape CONFIRMED by derivation, NOT landed, NOT verified.** Next
lane needs (a) a deployed self-hosted binary and (b) to first establish whether
`get_args()`'s call expression carries a recorded `Array` HIR type — check that
BEFORE writing the guard, because the whole fix hinges on it. Family the
reproducer must cover once an engine exists: zero args, one arg, many args, and
the `?? []` coalescing path itself.
