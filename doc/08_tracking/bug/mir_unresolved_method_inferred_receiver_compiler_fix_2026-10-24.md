# MIR "unresolved method call" on inferred receivers: compiler fix (2026-10-24)

Companion to the source-workaround record
`mir_unresolved_method_inferred_receiver_2026-10-24.md` (sibling lane
`simple-p3wa-method`). This record covers the root cause in `50.mir`.

## Symptom
Phase-3 run-11, `[go-to-end] failed stage=mir`:
`MIR lowering error: unresolved method call: <m>` (is_err / unwrap_err / unwrap /
bytes / len / get_or / ...), each preceded by the const-0 placeholder warning.

## Repro (red on stage2 p2shard-6, 1 s, <100 MiB)
Probe sources are kept outside the tree. `native-build` on a fresh worktree stops
at SCV admission, so the repro uses `compile` (the same MIR lowering):

    simple compile <probe>.spl --format=smf -o out.smf    # SIMPLE_LIB=<worktree>/src

| shape | red error |
|---|---|
| `val r = if val h = x: obj.lower(h) else: Err("..")`, then `r.is_err()` / `r.unwrap_err()` / `r.unwrap()` | unresolved is_err / unwrap_err / unwrap |
| `val rel = s.substring(..)`, then `rel.bytes()` | unresolved bytes |
| `val rel = s.substring(..)`, `val t: text = rel`, then `t.bytes()` | unresolved bytes |
| `val args: [Op] = raw_args` (`raw_args: i64`), then `args.len()` | unresolved len |
| `val n = d[k]` (`d: Dict<i64, text>`), then `n.unwrap()` | unresolved unwrap |

Control (green): both if-arms typed calls; `val r = obj.m()` / `T.open(p)`
with a direct `r.is_err()`.

## Root causes
1. **If/match merge with an untyped Result constructor arm**:
   `remember_merged_arm_identity` (`50.mir/mir_lowering_stmts.spl:3292`) adopts
   a HIR type only when EVERY arm has one. Untyped `Ok(..)`/`Err(..)` go through
   `lower_enum_construct_named` (`_MirLoweringExpr/switch_operators_calls.spl:5712`),
   which records no HIR type for `Result`. So the merge slot stays untyped and
   every Result method on it is unresolved.
2. **The untyped Let `Infer` marker beats real information**: HIR gives an
   untyped `val` the `Infer` marker as its Let type
   (`20.hir/hir_lowering/statements.spl:69 binding_payload_type`). The early-Let
   arm (`mir_lowering_stmts.spl:~1602`) then (a) remembers `Infer` on the binding,
   and (b) for an annotated `val t: T = init` copies the init local's HIR type
   over `T` whenever the init has ANY type, including `Infer`, or an erased
   `i64` handle under an `[T]`/`Dict` annotation.
3. **`.bytes()` treats any declaration as authoritative**
   (`_MirLoweringExpr/method_calls_literals.spl:~2572`): an `Infer` placeholder
   counted as a non-text declaration and blocked the lowered-local text proof.
   This is the d99d86670ee fix, which landed on release/1.0 in #4278 but is not
   in b0e68142332. It is ported here.

## Fix
- `untyped_result_ctor_locals` (new `MirLowering` field; it is initialised,
  reset per function and saved/restored around trait thunks). It is set for
  untyped Result constructors.
- `remember_merged_result_ctor_arm_type`: when not every arm is typed, the slot
  adopts the typed arms' type only if every untyped arm is an untyped Result
  constructor, all typed arms are equal, and that type is `Result`. In every
  other case nothing changes.
- `let_declared_type_override_v1`: an annotation wins over an init HIR type of
  `Infer`/`Error`. A `[T]`/`Dict` annotation also wins over an `i64`/`any`
  init, and the binding is then marked as a runtime array or dict. Any
  informative init type is still copied, as before.
- d99d port: for `.bytes()`, only a Str or Named declaration is authoritative.

## Not fixed (source workaround still needed)
- `d[k]` then `.unwrap()` (codegen.spl:592, type_infer/context.spl:136):
  `d[k]` lowers to a raw `V` read, not to `V?`
  (`lower_dict_runtime_read`, as_option=false). This is a source type error
  that the compiler rejects loudly. Use `d.get(k)` or an explicit `V?` local.
- `if c: x else: nil` in safe code (vhdl_call_lowering, driver_aot_native_output):
  `remember_merged_optional_arm_type` deliberately refuses a `nil` arm outside
  `unsafe`, following the "never widen nil" rule. The source must annotate the
  binding or use `None`.
- `.map(..).sum()/.max()` closure chains, `(a - b).max(0)` on binary
  receivers, module `var` Dict `get_or`, and `static fn` misuse (lean):
  these are not covered here.
- linker/link.spl `val r = self.m()` Result sites: these do not reproduce in
  isolation (the control is green). They are context-dependent and not
  diagnosed.
- backend/env.spl:224-249: `Backend` has none of those methods, and the dead
  `HirVisitor` was deleted by the sibling.

## Verification
Red was observed with the probes above. **The fix is unverified by execution**:
no producer carrying it exists, Stage 2 must not be rebuilt in this lane, and
the seed-interpreter route fails early (`rt_thread_id expects 1 argument`).
Regression spec: `test/01_unit/compiler/mir/inferred_receiver_method_resolution_spec.spl`
(UNEXECUTED).
The spec passes on the interpreter whether or not the fix is present. It only
discriminates when the file is compiled natively (same as the d99d precedent).

Two links are reasoned from the code, not observed:
- An untyped `val rel = s.substring(..)` binding inherits the `Opaque("str")`
  MIR type through the early-Let `local_is_str(init_local)` effective-type
  branch (`mir_lowering_stmts.spl:~1479`). So the d99d fallback proves it is
  text.
- The if/match arm locals pushed to `merged_arm_locals` are each arm's own
  result local, not a copy. So the constructor marker is seen.

The second Let arm (`mir_lowering_stmts.spl:~1850`) is not mirrored. Its own
comment says it is dead for Let, because the early arm handles every Let.
