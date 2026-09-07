# riscv64 freestanding: `text != ""` is TRUE for a zero-length text

- Status: **OPEN** — codegen defect, not fixed. One call site was repaired
  (see below); the comparison itself is still wrong everywhere else.
- Date: 2026-09-01
- Measured in-guest under real OpenSBI v1.4 `-bios fw_payload` (never
  `-kernel`, never `isa-debug-exit`), nonce `919b943728da5c1c`, lane
  `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`
  row 2, gate selftest OK (23 fixtures), freshly built Rust seed.

## The measurement

An in-memory branch trace inside the real
`module_decl_at` (`src/compiler/10.frontend/core/_Ast/module_state.spl`)
recorded, for a MISSING environment entry:

```
trace=900    entered the env-first tail with index 0
trace=800    env_value.len() == 0      <- the text IS zero length
trace=700    the `env_value != ""` arm was taken ANYWAY
```

`.len()` and `!=` disagree about the same value in the same expression, in the
same boot. `.len()` is the one telling the truth.

## Why this is expensive rather than merely wrong

`if x != "":` is the ordinary way to ask "is this text non-empty" and it
appears throughout the compiler. On this lane it is a constant `true`, so every
such guard falls into its non-empty arm carrying an empty value. In
`module_decl_at` that meant returning `ast_parse_i64("") == 0` for EVERY index,
so a module with N top-level declarations converted as N copies of its first
one — silently, with zero errors from either lowering stage. It cost four
boots and three prior sessions to find, because the failure surfaces as a
missing `main` several stages downstream.

## What is known and not known

- **Known:** `.len()` on the same value is correct (0). `ast_parse_i64("")`
  correctly returns 0 via its own `raw == ""` guard, so `==` against the empty
  literal appears to work where `!=` does not — but this is ONE observation and
  is not established as a general asymmetry.
- **Known:** the value came from `rt_env_get(key) ?? ""` where `rt_env_get`
  returned nil; probe2 confirmed `?? ` fires (a `?? "<NIL>"` printed `<NIL>`).
  So the operand is whatever `??` yields for the `""` literal.
- **NOT known:** whether the defect is in `??`'s materialisation of the literal,
  in text `!=` lowering, or in an identity-vs-content comparison. A verbatim
  replica of the same source in a DIFFERENT module compiled into the same image
  answered CORRECTLY, which points at something context-dependent (literal
  pooling / interning) rather than at the operator alone. Do not assume; the
  last four assumptions on this lane were all wrong.

## Repaired call site (not a fix for this bug)

`module_decl_at` now asks `env_value.len() > 0`. That repairs the declaration
loss and preserves hosted semantics exactly, but it does not fix the
comparison, and every other `!= ""` in the tree is still affected on this
target.
