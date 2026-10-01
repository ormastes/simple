# Seed collection HIR integration evidence

Scope: bootstrap seed repair only. No full Stage 2 build or release acceptance
is claimed by this focused report.

## Provenance

- Base: `cd1ad29fac9f4002e1729ddd8723c036dc6db074` (Result projection PR #1451).
- Worktree: `D:/wk-seed-collection-hir-integrated-20260923`.
- Branch: `fix/seed-collection-hir-integrated-20260923`.
- Earlier candidate: `0b1656f7a65` through `0d81af0c490` from the separate
  `D:/wk-seed-collection-typing-20260923` lane.
- Private Cargo target: this worktree's `build/cargo_target`.
- Compiler test executable SHA-256:
  `AAC1FAAF87A4D4B6ADE505042956E8379A0F06F7326A14CB2E9218F710774AB9`.

## Implemented contract

The landed Result checked projections remain intact. The existing contextual
lambda parameter mechanism now covers filter and both array-sort parameters;
map's resulting array element type comes from its callback return type.
Indexed fields consequently retain their declared owner, including through
Result projection, filter, map, and index combinations.

Unwrap of a nullable named struct or enum evaluates its receiver once in HIR
`LetIn`. `rt_is_none` selects the absent arm, which creates canonical hashed
Option.None with existing `rt_enum_new` and calls `rt_unwrap_or_trap`. The
present arm calls existing `rt_unwrap_or_self` with the declared inner type.
Scalar nullable lowering remains unchanged.

The prior candidate's new C/Rust/Pure-Simple nullable runtime helper, symbol
registration, and MIR dispatch changes are not carried forward. This repair
does not introduce a new runtime ABI or require a new dual-run shadow entry.

## Focused verification

MSVC `vcvars64.bat`; `SIMPLE_NO_STUB_FALLBACK=1`; offline locked dependencies.

- `cargo test -p simple-compiler --lib stage2_ --locked --offline --jobs 24`:
  **13 passed, 0 failed**, including HIR owner typing, combined Result/collection
  lowering, receiver-once structure, MIR calls, and native JIT execution.
- Four exact existing Result projection tests in that same executable:
  **4 passed, 0 failed**, including wrong-variant traps and nested Option payloads.
- Actual JIT execution preserves raw and Some-wrapped user enum values named
  Ok, Err, and None; unwraps exactly one nested Option envelope; and traps for
  raw nil and canonical None in subprocesses with unwrap diagnostics.
- Zero, false, and empty-text words are tested at the runtime ABI of the named
  unwrap function, both raw and Some-wrapped. This is not a claim of expanded
  source-level scalar nullable support.
- `direct-env-runtime-guard.ps1 --working`: PASS.
- Executable `*_spec.spl` files beneath `doc/06_spec`: **0**.
- Two build/verify cycles were used: the first stopped on a missing closing
  brace in the new helper; the second passed. No green tests were repeated.

Logs remain at `build/native_probe/stage2-focused.log`,
`build/native_probe/stage2-focused-cycle2.log`, and
`build/native_probe/result-projection-focused.log` in the isolated worktree.
Independent review and the coordinating lane's subsequent full Stage 2 build
remain required before landing or declaring the bootstrap repaired.
