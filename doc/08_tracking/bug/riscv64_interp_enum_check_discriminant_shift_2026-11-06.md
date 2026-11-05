# riscv64 in-guest enum check discriminant arrives shifted one nibble — interpreted `print` renders `<unknown>`

Date: 2026-11-06
Lane: `work/riscv-interp-string-tag-20261106` (PR #7045+1)
Gate: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`
(interp row: the interpreted hello world must print
`HELLO_INTERP_SIMPLEOS_RISCV64_OK nonce=<NONCE>` itself)

## Symptom

With the in-guest interpreter running the hello world end to end
(`[interp] hir ready, invoking InterpreterBackendImpl.interpret_hir_module`,
interpreted `main` executes), both interpreted `print` statements rendered
`<unknown>` instead of the marker text. The gate's nonce check cannot pass.

## Measured facts (RSP, `scripts/debug/rsp_watch.py`, laneO kernel)

1. `InterpreterBackendImpl.try_call_builtin`'s Print case reaches the
   `case _:` fallback every time: `value_to_string` was hit 25x with the
   identical argument and `rt_print_value` was never called. Serial showed
   nothing after `[interp] hir ready` in the stubbed run.
2. The fallback's text is `"<" + value.type_name() + ">"`, and
   `Value.type_name()` answers `"unknown"` only when its 20-arm match ALSO
   falls through every arm — so the `Value` discriminant test fails
   universally in this closure, not just for `String`.
3. Disassembly of the winning link copies (`kernel.elf`):
   - constructor `backend_value_string_v1` calls
     `rt_enum_new(enum_id=0x4f812a4, disc=0xe0f5dd50, payload=text)`
     (lui/addi materialization, unshifted). `rt_enum_new` stores the
     discriminant as a raw u32 at offset 0xc (`sw`).
   - `rt_enum_check_variant` (0x802028d0) loads the discriminant with `lwu`
     (zero-extend) and compares it against the FULL 64-bit third argument.
   - the match-side call in `value_to_string` passes
     `a2 = 0xe0f5dd500` — the constructor's discriminant constant shifted
     left 4 (`lui 0xe0f6; addi -0x22b; slli 4`). 0x...50 zero-extended can
     never equal 0x...500, so every arm test answers 0.
4. The ctor's constant is NOT `DefaultHasher("String")` (0x798698b3 with
   the str 0xff sentinel), nor FNV/djb2, nor a positional-registry index:
   it is the build's registry-resolved variant hash (registration-order
   dependent, see `enum_bare_name_collision_registry_2026-08-01.md` and
   #6953). Both sides therefore baked the SAME base constant; only the
   check side carries an extra `slli 4` at the call site.
5. The seed source has NO `<<4` on any enum-discriminant operand
   (checked `hir/lower/expr/control.rs` `subpattern_condition`,
   `codegen/instr/pattern.rs`, `codegen/instr/closures_structs.rs`,
   `codegen/instr/calls.rs` — all emit raw `iconst` of the hash). The
   shift appears between MIR and the emitted riscv64 code on this closure.
6. Discriminant 0 survives (`Ok`/`Some` checks pass: `0<<4 == 0`), which is
   why the outer `match interpreted: case Ok(_)` printed
   `[interp] interpreter returned Ok` while every non-zero-disc arm failed.

## Impact boundary

Every `match`/`is` arm test on an enum variant with a non-zero runtime
discriminant in this closure is at risk of the same shifted operand; the
observed blast radius in the interp row is the whole `Value` match family
(print dispatch, `type_name`, `value_to_string`). The nonce-dependence of
the surrounding control flow (laneN with nonce d6e3… ran `main` to
completion twice and exited rc=0; laneO with nonce 4c50… re-evaluated the
same print statement forever) shows downstream fall-through behavior is
data-dependent, consistent with the documented ANY-erasure /
wrong-field-resolution family rather than a second distinct defect.

## Fix in this lane (product side, tagged @workaround)

`src/compiler/70.backend/backend/interpreter_calls.spl` Print/Println:
identity-check the argument against a freshly constructed
`backend_value_string_v1("")` probe by RAW discriminant
(`rt_enum_discriminant`, both sides stamped by `rt_enum_new` at runtime so
they always agree) and print the raw payload via `rt_print_value` /
`rt_println_value`. Non-enum answers (-1) never match the probe. This is
the same identity-by-construction pattern `cranelift_codegen_adapter.spl`
already uses for `MirInstKind` dispatch. The `Value` match remains in place
under `else` for the other variants.

## Second layer, measured the same day: the exec loop re-reads one statement

With the fast path in the kernel, two nonce-dependent behaviors appear:

- nonce 07d9f42e…: boot completes — `<unknown>` twice, rc=0 — but the fast
  path did NOT fire (the interpreted arg is a `Value.String` built by the
  same shared `backend_value_string_v1` as the probe, so runtime discs must
  agree; the compiled `==` almost certainly mis-lowers on this closure, the
  same seed codegen rot as below).
- nonce 4c509e68…/fresh: 40 consecutive `rt_enum_discriminant` hits all on
  the SAME statement object (0x88ebab31) — `exec_stmt` re-dispatches one
  statement forever and the print is never reached.

The statement object itself is well-formed ({HEAP_ENUM, size 0x18,
enum_id == discriminant == 0x4aba51ce, payload}); the loop that should
advance past it does not. This is the documented ANY-erasure /
wrong-field-resolution seed defect family at the exec layer
(`interpreter.spl` exec loop), data-dependent on heap layout — the same
class the `process_module` comments describe for `module.functions`.

## Seed-side defects (recorded, NOT fixed in this lane)

1. The extra `slli 4` on the baked discriminant operand of
   `rt_enum_check_variant` call sites in the riscv64 cranelift path
   (evidence above). Needs the cranelift emission investigation with the
   clif in hand (SIMPLE_DUMP_CLIF).
2. The exec-loop statement-advance miscompile (nonce-dependent infinite
   re-dispatch of one statement).
3. Whoever fixes (1) must also decide the zero-vs-sign-extension split
   between the duplicate `rt_enum_check_variant` copies (the winning
   in-guest copy zero-extends with `lwu`; `baremetal_stubs.c`
   sign-extends; hashes with bit 31 set make these observably different).

All three are the same unbounded-in-a-guest-lane class as the par_state
seed layer (see
`riscv64_in_guest_parse_recursion_par_state_uninit_2026-11-05.md`).

## Verification

- Kernel build PASS, both rows, every cycle (laneO seed built from this
  branch only).
- OpenSBI boots: parse → desugar → hir ready → interpreted `main`
  executes (both prints, Ok, rc=0) for some nonces; exec-loop hang for
  others. The interpreted marker text does NOT yet reach serial; the
  gate's nonce check therefore still fails (see the lane's PR body for
  the gate verdict and transcripts under /tmp/rv-boot/).
- In-guest cycles used: 2 rebuild+boot cycles plus 7 RSP measurement
  sessions (no rebuilds).

---

## 2026-11-06 — CORRECTION (lane `work/riscv-disc-shift-fix-20261106`, PR #7051+1): the `slli 4` was a HAND-DECODE ERROR; there is NO emitter shift bug

The title defect of this record is WITHDRAWN. Re-examination with the
host-side fast loop (`SIMPLE_DUMP_CLIF`, `--no-incremental` — the dump only
fires when the module is actually compiled; the incremental cache otherwise
silently skips it) shows:

1. **CLIF is clean.** `InterpreterBackendImpl.value_to_string`'s clif
   contains `iconst.i64 0xe0f5_dd50` (raw hash) feeding
   `call rt_enum_check_variant(value, iconst 0x04f8_12a4, iconst 0xe0f5_dd50)`
   directly. No `ishl` anywhere in the function. (Also visible: the dead
   `iconst 0x751e_8de0` = bare-"Value" id that the site-16 remap pass
   correctly replaces with the qualified `0x04f8_12a4` in the live operand.)
2. **The machine code is a correct 3-instruction materialization.** The
   laneO decode read `lui 0xe0f6` as producing `0xe0f5dd50`; it produces
   `0x0e0f6000` (bit 31 clear — no sign extension), `addi -0x22b` gives
   `0x0e0f5dd5`, and `slli 4` gives `0xe0f5dd50` — exactly the raw
   discriminant. Cranelift factored out the low zero nibble; the factoring
   is exact. `0xea11_d77b`-style bit-31 constants take the constant-pool
   load path instead (verified on a minimal collision-enum repro); both
   paths were verified correct on the object code.
3. **Live in-guest (RSP, laneP kernel):** `rt_enum_check_variant` receives
   objects whose stored `enum_id`/`discriminant` EQUAL the baked expected
   operands (`exp_enum_id=0xe906403, exp_disc=0x0`, object
   `{type=7, enum_id=0xe906403, disc=0x0}`) — the check ABI agrees in-guest.

So the previous section's root cause is dead. What remains real, measured:

- **Exec-loop re-dispatch:** the same statement object is re-checked
  forever on hanging nonces (24+ identical check hits on one object).
- **The laneO `<unknown>` observations:** with correct operands and
  matching objects, the print-time `Value` checks still need live
  re-verification; the interpreted arg binding (`val arg: Value = args[0]`,
  an ANY-erased list element rebind) is the prime suspect for what the
  check actually receives at print time.
- The zero- vs sign-extension note on duplicate `rt_enum_check_variant`
  copies still stands as hardening work, but it is not the gate blocker.

The @workaround fast path in `interpreter_calls.spl` (PR #7051) is
unaffected: it remains a valid identity-by-construction robustness pattern,
just not the fix for a non-existent shift bug.

Boot evidence added the same day: a completing nonce (aa11bb22…, laneP
kernel WITH the #7051 fast path) still renders `<unknown>` twice with rc=0 —
so the print-time failure is NOT operand materialization; the interpreted
arg binding (`val arg: Value = args[0]`, ANY-erased list rebind) is the
prime suspect for what the check actually receives. Also observed:
`cargo test -p simple-compiler enum` fails
`seed_builtin_discriminants_are_the_declared_ordinal` ONLY under the
multi-test filter (registry pollution by a same-process sibling test) and
passes isolated — a second, in-tree manifestation of the
registration-order-dependent-discriminant fragility (#6953 family), not a
regression from this lane (no seed change shipped here).

---

## 2026-11-06 — OK-WRAPPER LEAK FIXED (lane `work/riscv-args-binding-20261106`, PR #7051+3): `.unwrap()` returned the Ok-wrapper itself; interpreted prints now render REAL text

Root cause of the print-time fall-through, measured end to end:

1. `backend_value_string_v1`'s CLIF is correct —
   `rt_enum_new(0x04f8_12a4, 0xe0f5_dd50 as i32, text)` — and
   `try_call_builtin`'s Value-arm tests carry the matching constants.
2. Live, the print arg object was `{HEAP_ENUM, enum_id=0, disc=0,
   payload=text}` — that is `rt_enum_new(0, 0, payload)` = **Result.Ok**:
   `val v: Value = evaluated_arg.unwrap()` in interpreter_expr.spl's Call
   arg eval returned the Ok-WRAPPER, not the payload, on the riscv64
   in-guest AOT path. `args[0]` was therefore a Result, every `case
   Value.X` test failed (Value's enum_id is 0x04f8_12a4, not 0), and
   `type_name()` answered "unknown" — the `<unknown>` tail in full.
3. Fix (tagged @workaround bug=riscv64_interp_ok_wrapper_leak_2026_11_06):
   extract the payload with an explicit `match evaluated_arg: case
   Ok(inner_v): inner_v` — the rt_enum_check_variant + rt_enum_payload
   binding pattern `cranelift_codegen_adapter.spl` already uses; Result
   lives in the untyped id-0 lane whose checks measure passing in-guest.

Verification (nonce aa11bb22cc33dd44, completing): interpreted prints now
emit REAL TEXT — `HELLO_INTERP_SIM` twice, rc=0 (was `<unknown>`).

## NEXT TAIL, precisely measured the same session: interpreted string literals truncate to 16 chars in-guest

The printed text is exactly 16 chars: the string object passed to
`backend_value_string_v1` is genuinely `{type=1, size=33, len=16}` with
zero padding after "HELLO_INTERP_SIM" — a true construction-time
truncation in the guest frontend's literal lexing/slicing (the enclosing
source text is complete: parsing finds the closing quote and the second
print statement). The gate's nonce marker still cannot pass until this is
fixed. Exec-loop re-dispatch (the earlier defect 2) is bounded on
completing nonces (the Print case re-enters many times — 60+ probe
constructions observed — but the run finishes with exactly two prints);
unbounded on hanging nonces. Both recorded for the next lane.

---

## 2026-11-06 — 16-CHAR LITERAL TRUNCATION FIXED (lane `work/riscv-string-trunc-20261106`, PR #7051+4): the winning duplicate `rt_array_push` never grew; default cap is 16

Measured chain (RSP write-watchpoint on the result object at 0x80e6c5d0 —
stable across boots — caught `rt_string_concat` mid-copy; the concat's own
frame held `HELLO_INTERP_SI` (15) + `M` (1)):

1. `lexer_struct.spl scan_string` builds token text via
   `parts.push(advance())` char-by-char, then `parts.join("")`. `var parts:
   [text] = []` lowers to `rt_array_new(0)`.
2. Winning in-guest `rt_array_new` (disasm): `cap = raw_or_encoded(0); if
   (cap == 0) cap = 0x10` — DEFAULT CAPACITY = 16.
3. Winning in-guest `rt_array_push` (disasm, the ghdl TU's copy):
   `if (len >= cap) return 0` — NO GROWTH, silently drops. Pushes 17..56 of
   the 56-char literal vanished; join produced exactly "HELLO_INTERP_SIM".
   Same defect family as #7044 (duplicate-TU lottery): the stubs and
   baremetal_runtime_core.inc.c copies both delegate to a GROWING
   rt_array_push_handle (cap*2, 4096 ceiling); only the ghdl TU carried the
   pre-fix no-growth body.

Fix: mirrored the growing `rt_array_push_handle` into
`ghdl_boot_info_runtime.c` verbatim (its rt_array_push now delegates), with
the incident comment — all three runtime TUs now grow regardless of which
wins the link.

Verification (nonce aa11bb22cc33dd44): interpreted prints render the FULL
marker — `HELLO_INTERP_SIMPLEOS_RISCV64_OK nonce=aa11bb22cc33dd44` and the
full second line, rc=0. Official gate verdict recorded in the PR.
