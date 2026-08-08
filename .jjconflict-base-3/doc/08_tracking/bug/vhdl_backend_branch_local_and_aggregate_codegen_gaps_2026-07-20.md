# VHDL backend: branch-local computation / struct-aggregate / array-aggregate codegen fails (9 examples)

- **Date:** 2026-07-20
- **Status:** open
- **Area:** `src/compiler/70.backend/backend/vhdl_expr.spl` and sibling VHDL
  backend files under `src/compiler/70.backend/backend/` (pure Simple, not
  the Rust seed).

## Context

`test/02_integration/compiler/.spipe_matchers_vhdl_backend_e2e_spec.spl` had
22 failures, all `semantic: unknown variant or method 'Return' on enum
MirTerminator` — a plain stale-test rename (`MirTerminator.Return(...)` ->
the current variant name `MirTerminator.Ret(...)`, see
`src/compiler/50.mir/mir_instructions.spl:570`). That rename was applied
(mechanical, 35 occurrences, `sed`-equivalent `replace_all`) and is a
legitimate value-preserving fix — it dropped failures from 22 to 9. The
remaining 9 are genuine VHDL backend defects, unrelated to the rename.

## Remaining failures (after the `Return`→`Ret` fix)

```
✗ compiles branch-local computations inside combinational process
  expected false to equal true
✗ compiles branch-local VHDL resize slice and concat inside combinational process
  expected false to equal true
✗ compiles branch-local VHDL signal and variable assignments inside combinational process
  expected false to equal true
✗ compiles switch targets with computations inside combinational process
  expected false to equal true
✗ compiles struct aggregate to named record assignment
  expected library ieee; ...   (VHDL source text mismatch)
✗ compiles branch-local struct aggregates inside combinational process
  expected false to equal true
✗ compiles array aggregate assignment
  expected false to equal true
✗ compiles struct type to VHDL record package
  expected library ieee; ...
✗ compiles enum type to VHDL enumeration
  expected library ieee; ...
```

Two failure shapes:
1. `expected false to equal true` — the spec's `check_msg(result.is_ok(), "...")`
   assertion fails, meaning `backend.compile(module)` returns an `Err`, i.e.
   the VHDL backend rejects MIR it should accept (branch-local temporaries /
   struct-aggregate / array-aggregate assignments inside a combinational
   process block).
2. `expected library ieee; ...` — backend compiles successfully but the
   generated VHDL source text differs from the expected golden text (struct
   record package / enum-to-VHDL-enumeration / struct-aggregate-to-record
   codegen shape has drifted from what the spec expects).

## Command

```
SIMPLE_RUST_SEED_WARNING=0 timeout 40 bin/release/x86_64-unknown-linux-gnu/simple test test/02_integration/compiler/.spipe_matchers_vhdl_backend_e2e_spec.spl --no-session-daemon
```

## Not attempted

This is deep pure-Simple compiler backend logic (VHDL synthesis lowering),
not a spec-level fix — out of scope for a test-triage pass. No src/**
behavior change attempted beyond the unrelated `Return`→`Ret` spec rename
noted above. Needs a compiler-backend engineer to compare
`backend.compile()`'s branch-local/aggregate lowering against the VHDL
combinational-process codegen path in `src/compiler/70.backend/backend/`.
