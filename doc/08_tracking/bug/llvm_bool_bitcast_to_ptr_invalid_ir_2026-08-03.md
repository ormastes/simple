# Pure-Simple LLVM shard emits invalid `bitcast i1` to `ptr`

- **Date:** 2026-08-03
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** P1
- **Area:** pure-Simple LLVM MIR lowering
- **Verified owner:**
  `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl::value_as_type`
- **Reproducer:** `src/lib/nogc_async_mut/env/paths.spl` compiled as the
  focused pure-Simple Stage 4 shard

## Reproduction

The diagnostic compiler was a freshly rebuilt pure-Simple Stage 3
(`725 compiled, 0 failed`) targeting `x86_64-unknown-linux-gnu`. It compiled
`src/lib/nogc_async_mut/env/paths.spl` as a single positional native-build
input, which `bootstrap_main.spl` routes through the in-process pure-Simple
CompilerDriver. `SIMPLE_BOOTSTRAP_STAGE4` was not set and the command did not
pass an explicit entry-closure flag. After the separate target-triple lifetime
repair, this focused shard emitted a valid LLVM header and reached `llc`.

`llc` then rejected `/tmp/simple_llvm_3450082.ll` at line 2874, column 19:

```llvm
%t281 = bitcast i1 %l162 to ptr
```

The diagnostic is `invalid cast opcode for cast from 'i1' to 'ptr'`. This is a
new downstream blocker; it is not a recurrence of the former
`<invalid-heap:...>` target triple.

## Root-cause direction

`translate_terminator` routes return coercions through `value_as_type`, whose
generic cast selector falls back to LLVM `bitcast` whenever no known cast
matches. LLVM does not permit an integer boolean to be bitcast to a pointer.
Adjacent comparison lowering already records the valid conversion shape:
zero-extend `i1` to the target native integer, then use `inttoptr`.

Do not weaken LLVM verification or replace the value with zero. A repair must
preserve the boolean value, handle the reverse pointer/integer neighbor where
applicable, and add exact plus adjacent lowering tests before retrying only the
failed shard.

The focused regression models a defined SSA value only. The observed
`env/paths` diagnostic IR also contains a separate upstream missing-store/value
loss defect; legal cast emission must not be used as evidence that that defect
is fixed.

## Verification

`llvm_bitcast_pointer_bool_spec.spl` passes all four focused examples in strict
interpreter mode: exact `i1 -> native-int -> ptr`, reverse `ptr -> i1`
truthiness, and adjacent `i64 -> ptr` / `ptr -> i64` conversions. Unsupported
value coercions now fail closed instead of falling through to `bitcast`.

This result closes only the LLVM cast-emission defect. It does not claim the
separate `env/paths` missing-store/value-loss defect, shard, or full Stage 4 is
fixed.

## Regression fence added 2026-08-08

Per `doc/09_report/infra/aot_lane_regression_fence_audit_2026-08-07.md` row 7
("FIXED, but verified only once, no fixture — at risk of silent regression"):

**Audit correction:** the audit's "no dedicated minimal fixture" claim was
wrong — `test/01_unit/compiler/backend/llvm_bitcast_pointer_bool_spec.spl`
already exists and directly synthesizes the exact defect shape (a local of
MIR type `i1` flowing into a function whose ABI return type is `ptr` at
`Ret`, via `MirToLlvm`'s test-only visibility), asserting both the positive
emission (`zext i1 %l0 to i64`, `inttoptr i64 ... to ptr`) and the absence of
the illegal `bitcast i1 %l0 to ptr`. The audit searched `scripts/check/` and
`test/fixtures/` and missed `test/01_unit/`. The real, narrower gap: that
spec only string-matches the emitted IR text — it never feeds the module
through the actual LLVM verifier (`llvm-as`/`opt -passes=verify`), so a
regression that still produces *some* IR would not necessarily be caught if
the string patterns happened to still match, and there is no fence at all
that both drives real `native-build` and validates the emitted module with
the real verifier.

**What was added:** `scripts/check/check-native-option-bool-llvm-verify.shs`
+ `test/fixtures/native_option_bool_llvm_verify/main.spl` (a function
returning `Option<bool>`, which boxes its payload behind the runtime's
uniform tagged-pointer representation — a real bool-crossing-a-`ptr`-boundary
AOT case). The script runs `native-build` with `SIMPLE_LLVM_BITCODE_DEBUG=1`
(real `llvm-as` + `opt -passes=verify` against the actual emitted module, not
a hand-written stand-in), asserts the binary's output matches the
interpreter reference, and asserts (defense in depth) that the dumped `.ll`
contains no `bitcast i1 ... to ptr`.

**Known limitation, stated explicitly (do not read past this):** inspecting
the emitted IR with `SIMPLE_KEEP_LLVM_IR=1` / `SIMPLE_LLVM_BITCODE_DEBUG=1`
confirmed this fixture does **not** force the exact `i1 -> ptr` bitcast MIR
shape. `rt_enum_new` (the boxing call `Option<bool>` lowers through) is
declared to accept an `i1` payload argument directly, so the bool crosses as
a same-typed call argument — `value_as_type(_, "i1", "ptr")` is never
invoked for this fixture. The only `ptr` conversions observed in its IR are
`inttoptr i64 ... to ptr` (the *adjacent*, always-legal case), confirmed by
`grep -n 'bitcast\|inttoptr\|zext i1' <dumped .ll>`. Every attempt this
session to force the exact scenario through ordinary supported surface
syntax failed or was refused: user-defined generics are hard-rejected on the
native-build path (`generic functions are not supported on the native build
path yet ... monomorphization is not implemented (#158 Phase B)`), and a
`bool?` nullable-return variant compiled but diverged from the interpreter on
an unrelated equality-representation question (not chased further — see
below) without ever emitting the target bitcast either. The compiler's own
comment at `core_codegen.spl:1031-1040` ("nothing upstream actually
materializes the cast this edge assumed, so emit it here") indicates the
fix is a corrective net for a shape normal codegen paths prevent by always
boxing first; the exact positive-emission trigger may not be reachable
through ordinary supported `.spl` source at all, which is why the unit spec
synthesizes it directly instead.

**Net effect:** this new gate proves the LLVM backend's bool/ptr-crossing
family produces a module the real LLVM verifier accepts on a live
`native-build` path (something nothing did before today), and is a hard
regression fence on that. It is **not** proof that the exact `bitcast i1 ...
to ptr` line can recur and be caught by a live compile — that positive
coverage still rests entirely on the interpreter-executed unit spec's string
match. Closing that residual gap would require either a monomorphization
fix that unblocks a generic-function repro, or a native-build-reachable API
to invoke `MirToLlvm.translate_terminator` directly (blocked today: `method
translate_terminator not found on type MirToLlvm` from outside the
test-only-visibility path).

**Side finding, not chased (separate from row 7):** a `bool?`-returning
function compiled and ran under `native-build`, but `a == true` against the
nullable-bool result printed `no-match` where the interpreter printed
`match` — a real AOT-lane output divergence. This looks like it belongs to
the row-2 family (`native_inlined_option_return_representation_mismatch_2026-08-02.md`,
"`rt_native_eq` compares mismatched representations") with a bool payload,
but was not isolated or confirmed further this session and no new bug doc
was filed for it — flagging here so it isn't lost.

Sabotage-verified: mutating the fixture's expected output in the check
script produced `exit=1` with an explicit expected/actual mismatch message;
restoring it produced `exit=0` again. A hand-written two-line `.ll`
containing `bitcast i1 %b to ptr` was independently confirmed to be rejected
by `llvm-as` with the exact historical diagnostic (`invalid cast opcode for
cast from 'i1' to 'ptr'`), and the fixed `zext i1 -> i64` + `inttoptr i64 ->
ptr` shape was confirmed to pass `llvm-as` + `opt -passes=verify` — proving
the verifier mechanism this gate relies on actually discriminates the two
cases.
