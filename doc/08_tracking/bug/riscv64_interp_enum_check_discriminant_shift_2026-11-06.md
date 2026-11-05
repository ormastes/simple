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
