# LLVM text backend: array value-copy loop redefines an SSA local (llc: multiple definition of 'l15') (2026-08-22)

Filed: 2026-08-22
Status: RESOLVED (2026-08-22)
Severity: high — blocks native-build of any function that copies an array by value

## Symptom

```
fn main() -> i64:
    var xs = [1, 2]
    val t = xs
    xs.push(9)
    print "alias {t.len()} {xs.len()}"
    0
```

`bin/simple native-build --runtime-bundle core-c-bootstrap ...` →
`llc-20: simple_llvm_*.ll:95:3: error: multiple definition of local value named 'l15'`.
Reproduced on pristine `origin/main` 625c245bafa (after working around the
`hash_text` cache-load failure, see mir_unresolved_method_call_merge_2026-08-22.md).

## Cause (located, not fixed)

`val t = xs` lowers to a value-semantics copy loop (`rt_array_get` /
`rt_array_push` per element). The loop counter is a MIR local that is written
twice (`%l15 = add i64 %l16, 0 ; copy` in the preheader and
`%l15 = add i64 %l21, 0 ; copy` in the latch). The text LLVM backend emits MIR
`Copy` into an existing local as a new SSA definition instead of an alloca
store / phi, so any MIR local assigned in more than one block is invalid IR.
Same-shape `Copy` elsewhere (straight-line code) happens to be single-assignment
and passes. Fix belongs in `70.backend/backend/_MirToLlvm` (mem2reg-style
alloca for multiply-assigned locals) or in the copy-loop emitter.

Found while building the reproduce fixture for the `merge` bug; the aliasing
half of that fixture (`val t = xs; xs = xs + [..]; t unchanged`) is therefore
only verified on the interpret lane until this is fixed.

## Resolution (2026-08-22)

Root cause is NOT in the emitter: `ssa_alloca_transform_blocks`
(`src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`) rejected EVERY
function carrying a `Ret(Some(..))` terminator (`"unsupported value return
terminator"`, added by 9a0cfd1e5d6 as a staged-native payload guard), so no
multi-def local in any value-returning function was ever slotted. The phi
fallback (`ssa_var_transform_blocks`) does not handle the loop-carried copy
counter either, so the text backend emitted the second def verbatim. The
a8992dfe897 closure-diamond fix worked around this same restriction per site.

Fix (general, class closed): admit `Ret(Some(v))` through the same structural
operand-payload gate as `If`/`Switch` (`ssa_operand_local_payload_valid`, which
already nil-guards the staged-native wrapper), collect the returned local as a
use, and rewrite the ret operand with a slot Load. `ssa_term_has_value_return`
is deleted. MIR shape is unchanged; the pre-existing spec
`test/01_unit/compiler/mir_opt/ssa_alloca_value_return_slotting_spec.spl`
already demanded this behaviour.

Verified: `probe_array_value_copy_ssa.spl` native-builds (llc rc=0) and prints
identically to the interpret lane for int/text/struct alias copies and a copy
inside a value-returning fn. Specs:
- `test/01_unit/compiler/backend/llvm_array_value_copy_single_ssa_def_spec.spl`
  (5 cases, grep the emitted `.ll` for a single def per `%lN`; 5/5 fail pre-fix)
- `test/02_integration/compiler/backend/array_value_copy_native_spec.spl`
  (native-build + run + dual-run compare)
- `test/01_unit/compiler/driver/ssa_local_payload_source_spec.spl` updated to
  pin the new admission line instead of the deleted refusal.
