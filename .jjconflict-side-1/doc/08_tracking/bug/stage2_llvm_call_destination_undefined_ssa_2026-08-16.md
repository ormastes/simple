# Stage 2 LLVM Call destination is referenced without an SSA definition

- **Date:** 2026-08-16
- **Component:** pure-Simple Stage 2 MIR-to-LLVM text generation
- **Severity:** critical (blocks the Stage 2 probe and Stage 3 admission)
- **Status:** cycle-1 source fix pending static review; not verified
- **Category:** `C3 malformed_llvm_ir_undefined_ssa_local`

## Failure

The admitted Stage 2 compiler failed the immutable mixed-tail probe while
building LLVM text.  In `numeric_int_probe_status`, MIR local 17 is the result
of `has_call_indirect(function)`.  The generated function contains no call
definition for that result, then emits:

```llvm
%t6 = icmp ne i64 %l17, 0
```

`llvm-as` rejects the preserved IR at line 331, column 21 with `use of
undefined value '%l17'`.  This is a MIR-to-LLVM text-generation failure; LLVM
verification and `llc` target code generation are not reached.

## Root cause and cycle-1 fix

`MirToLlvm.translate_instruction_at` relied on structural pattern dispatch for
`MirInstKind.Call`.  The Stage 2 native enum ABI can retain the variant
discriminant while eroding that payload-pattern dispatch, selecting the
wildcard no-op and emitting no `%lN = call ...` line.  A later terminator still
formats the typed MIR local as `%l17`.

The cycle-1 fix in
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`:

1. recognizes `Call` by discriminant before the structural match;
2. decodes its destination, callee, and arguments with `rt_enum_payload` and
   `rt_tuple_get`;
3. marks the destination defined only after the call reaches the output sink;
4. fails immediately when a call destination was not emitted.

It does not replace a missing value with `0` or `undef`.

## Evidence

- Probe receipt:
  `build/native_probe/p4_mixed_tail_probe_s2new_20260816/receipt.env`
  (`454bf9c5f7c45a16340d5d7134937cdece9a6a37214362703c03e1c93215d5cd`)
- Preserved IR:
  `build/native_probe/p4_mixed_tail_probe_s2new_20260816/tmp/simple_llvm_566634.ll`
  (`dc0798ac988bef4e04457f8453e093296a550d0e840c0b97e12a2de011778cad`)
- Canonical replay receipt:
  `build/native_probe/p4_mixed_tail_probe_s2new_20260816/c3-replay-20260816-cycle1/receipt.env`
  (`0e263f28c1a4816bb309a767538cc0cc6ea489f76f6004822d37ad86ffdd92d4`)

The diagnostic lane and probe owner each consumed a replay after concurrent GO
and terminalization messages.  The replay receipt records
`aggregate_replay_count_known=2` and `protocol_exact_once_violation=true`; no
further replay is permitted for this evidence identity.

## Verification contract

The exact retained System reproducer is
`test/02_integration/compiler/bootstrap_mixed_tail_ret_probe.spl`.  A focused
integration spec for Call-result definition is held until the primary agent
freezes its REQ ID, literal SSpec names, helpers, provenance inputs, and
fail-fast contract.  After independent static review, verification may rerun
only the failed probe with the same private cache and immutable provenance.

## Separate blocker

The probe receipt also records 5,257 unresolved constant-zero placeholders and
`stub_guard_effective=false`.  Those warnings precede the `llvm-as` failure and
are not its cascade.  They remain the separate C4 fail-closed placeholder
category; a shared upstream cause has not been proven and is not claimed here.
