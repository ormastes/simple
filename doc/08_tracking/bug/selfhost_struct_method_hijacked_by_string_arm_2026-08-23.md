# Struct/class method hijacked by string-only MIR fallback arm (AOT SEGV, bootstrap phase 3 blocker)

- Date: 2026-08-23
- Severity: CRITICAL (blocked bootstrap phase 3; stage2 could not compile a three-line hello world)
- Status: FIXED (lowering); stage2/stage3 redeploy still required
  - History note: the lowering fix (`7127df8d794` predicate-shape widening,
    `ef3df4a785e` cross-module owner evidence) was silently reverted by
    `0299186137d`, so for a period this line read FIXED while `origin/main`
    carried the pre-fix narrow form — that disagreement is what identified the
    clobber. Restored byte-for-byte from `bf00d9197b7` by `8f84d2b19af`.
- Area: `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`

## Symptom (VERIFIED)

`/mnt/data/bootstrap-run28/stage2/x86_64-unknown-linux-gnu/simple` (132,930,184 bytes,
commit `9c5e2dad378`) SEGVs (rc=139) on a three-line hello world for BOTH supported
commands, in both configurations:

- `native-build hw.spl` -> rc=139, 1.66s (crash in the HIR cache encoder; separate defect D1)
- `SIMPLE_HIR_CACHE=0 native-build hw.spl` -> rc=139, 9.08s (this defect), crashing at
  step 5/6 `native_compile`.

## Classification (VERIFIED by gdb)

NOT the NULL-GOT class (`rip` is valid, not 0) and NOT the zeroed-payload class.
This is a third class: **bad-pointer deref of a non-pointer that codegen untagged.**

```
rip 0xa83bb8  compiler__driver__driver_aot_native_output___compile_frozen_module_capsule+120
r14 0xfffffffffffffff8   rax 0xffffffffffffffff
faulting insn:  mov (%r14),%rcx
```

Preceding instructions:

```
call   rt_string_find          ; returns -1 (not found)
mov    %rax,%r14
and    $0xfffffffffffffff8,%r14 ; untag as tagged pointer:  -1 & ~7 = -8
=>  mov (%r14),%rcx            ; read enum tag  -> SEGV on 0xfffffffffffffff8
```

Backtrace: `_compile_frozen_module_capsule` <- `CompilerDriver.compile_to_native`
<- `run_native_build_bootstrap` <- `main`.

The surrounding string literals identify the source exactly: lengths 21
(`"AOT compile error in "`), 23 (`": invalid-capsule-batch"`) and 19
(`": capsule-not-found"`). The `rt_string_find` call sits between those two `Err`
blocks -- precisely where `src/compiler/80.driver/driver_aot_native_output.spl:1099`
reads `val capsule = batch.find(name)`.

`batch` is a **class**, not text:
`FrozenNativeModuleCapsuleBatchV1.find(module_name: text) -> FrozenNativeModuleCapsuleV1`
is declared at `src/compiler/80.driver/driver_types.spl:97`.

**The compiler miscompiled itself.**

## Root cause (VERIFIED)

`method_calls_literals.spl` has a family of string-only fallback arms that map an
unresolved method onto an `rt_string_*` runtime symbol:

- `:1962` starts_with, `:2059` ends_with
- `:2300` contains / find / rfind
- `:2339` index_of
- `:2382` the 11-name text-special arm (trim, strip, lower, to_lower, to_upper,
  split, replace, rfind, find, contains, parse_f64), symbol table at `:2439`

**Every one of those arms already vetoes itself with `not predicate_has_custom_owner`**
so that a genuine user struct/class method keeps normal custom-method precedence.
That is the correct design and it was already written.

The defect is that the flag was only ever *computed* for three names.
`predicate_method_shape` (line 1199, pre-fix) read:

```
val predicate_method_shape =
    (method == "starts_with" or method == "ends_with" or method == "contains") and args.len() == 1
```

For every other name those arms can claim -- find, rfind, index_of, split, replace,
trim, strip, lower, to_lower, to_upper, parse_f64 -- the owner-recovery block never
ran, so `predicate_has_custom_owner` was **structurally always false**. The guard
existed; the evidence feeding it did not.

Consequence: any user struct/class method with one of those names is hijacked into
an `rt_string_*` call with the struct handle passed as a string pointer.
`rt_string_find` returns a plain i64 `-1` for not-found (that IS the language
contract), codegen untags it as the returned struct pointer, and dereferences -8.

Note this is the same defect *shape* the file already documents for array receivers
(`mir_string_arm_array_receiver_find_rfind_2026-08-01`, comments at `:2254-2300`).
That lane fixed the **Array/Slice** receiver case via `contains_recv_is_array`. The
**class/struct instance receiver** case was never covered.

## Fix

1. Broaden `predicate_method_shape` to the same name/arity set the arms below can
   claim, so the owner evidence is actually computed. Arities mirror each arm's own
   gate (find/rfind/contains/starts_with/ends_with: 1; index_of/replace: 2;
   split: 1 or 2; trim/strip/lower/to_lower/to_upper/parse_f64: 0).
2. The text-special arm's receiver was selected with
   `if method == "contains": prelowered_method_receiver else: self.lower_expr(receiver)`.
   Now that the probe pre-lowers for this arm's whole name set, keying off the
   method name would lower the receiver a SECOND time and duplicate its side
   effects. Changed to the `has_prelowered_method_receiver` pattern already used by
   the array probe above it.

No arm was deleted or disabled; no runtime symbol, ABI, or value-semantics
behaviour changed.

## Reproduce test

`test/01_unit/compiler/mir/struct_method_string_arm_hijack_source_spec.spl`

- Pre-fix: 5 total, **3 passed, 2 failed** (both mechanism scenarios red).
- Post-fix: 5 total, **5 passed, 0 failed**.
- Verified by reverting the source edit alone (`git checkout --`) and re-running.

The 3 behavioural scenarios (a `Registry` class owning `find`/`contains`/`replace`)
pass under the Rust seed both pre- and post-fix, because the seed's lowering is
Rust and unaffected. They are defect-class neighbours that bind once self-hosted.

## Limits (honest)

- The lowering fix is verified at source/mechanism level. **stage2 remains
  miscompiled** -- it was produced by a stage1 carrying the unfixed rule, so the
  SEGV persists in the existing binary until a bootstrap redeploy rebuilds it.
  An end-to-end "hello world compiles AND runs under a self-hosted binary" proof
  requires that redeploy and is NOT claimed here.
- D1 (the HIR cache encoder SEGV) is a **separate** root cause; see
  `selfhost_hir_cache_encode_hir_type_segv_2026-08-22.md`. One fix does not
  resolve both.
