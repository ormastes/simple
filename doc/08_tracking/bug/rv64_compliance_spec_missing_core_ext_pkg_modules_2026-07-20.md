# `rv64_compliance_spec.spl` imports modules that don't exist in `src/lib/hardware/rv64gc`

- **Date:** 2026-07-20
- **Status:** FIXED 2026-11-06
- **Area:** `src/lib/hardware/rv64gc/**` (pure Simple RISC-V RV64GC core model)

## Symptom

```
error: semantic: Cannot resolve module: hardware.rv64gc.core.rv64_execute
error: test-runner: no examples executed
```

## Command

```
SIMPLE_RUST_SEED_WARNING=0 timeout 40 bin/release/x86_64-unknown-linux-gnu/simple test test/02_integration/hardware/rv64gc/.spipe_matchers_rv64_compliance_spec.spl --no-session-daemon
```

## Root cause

`test/02_integration/hardware/rv64gc/.spipe_matchers_rv64_compliance_spec.spl`
imports:

```simple
use hardware.rv64gc.core.rv64_execute.{alu_execute, alu_execute_word}
use hardware.rv64gc.ext.rv64_muldiv.{muldiv_execute, muldiv_execute_word}
use hardware.rv64gc.ext.rv64_atomics.{amo_execute, AmoOp}
use hardware.rv64gc.pkg.rv64_types_pkg.*
```

None of `core/rv64_execute.spl`, `ext/rv64_muldiv.spl`, `ext/rv64_atomics.spl`,
or `pkg/rv64_types_pkg.spl` exist anywhere under `src/lib/hardware/rv64gc/`.
The directory only contains `__init__.spl`, `mod.spl`, and
`top/{__init__,mod,rv64_machine}.spl` — no `core/`, `ext/`, or `pkg/`
subdirectories at all, and grepping those files for `alu_execute`,
`muldiv_execute`, `amo_execute`, `AmoOp` finds zero hits. This is not a
rename/stale-import (no equivalent symbols exist elsewhere to redirect to) —
the ALU/mul-div/atomics/types-package submodules this compliance spec
exercises were either never implemented or were removed without deleting the
dependent spec.

## Not attempted

Implementing the missing RV64GC ALU/muldiv/atomics/types-package submodules
is a substantial feature-implementation task, out of scope for a test-triage
pass. Flagging for follow-up: either implement
`src/lib/hardware/rv64gc/{core/rv64_execute,ext/rv64_muldiv,ext/rv64_atomics,pkg/rv64_types_pkg}.spl`
to match what the spec expects, or retire the spec if RV64GC compliance
testing was superseded by `top/rv64_machine.spl`.

## Resolution (2026-11-06)

The root-cause section above was wrong: the modules were never missing, they
live in `src/hardware/rv64gc/{core,ext,pkg}/` (not `src/lib/hardware/...`) and
`hardware.rv64gc.*` resolves to them. On the Rust seed the spec already ran
20/22 (RED at this checkout: 2 failures, not 0/22). The two failures were spec
bugs: `(misa >> 5) and 1` / `(misa >> 3) and 1` used logical `and` (yields
`true`) instead of bitwise `&`. Fixed to `& 1`, assertions unchanged
(expect `== 1`). Result: 22/22 passed.

## Re-verification (2026-11-07, work/riscv-bugs-20261107)

Still FIXED at `origin/release/1.0.0` @ `1965f658d45`; no code change needed.
The spec file is `test/02_integration/hardware/rv64gc/rv64_compliance_spec.spl`
(the `.spipe_matchers_` name in the Command section above no longer exists).
Binary: privately built Rust seed `target-rv/release/simple` (54154944 bytes,
built 2026-11-07 08:56 from this tip; `cargo build --release --bin simple`).

```
simple test test/02_integration/hardware/rv64gc/rv64_compliance_spec.spl
SPEC FILE VERDICT: ... outcome=OK declared>=22 executed=22 passed=22 failed=0 skipped=0 dropped=0
```

Not verified on the pure-Simple self-hosted binary (none deployed in this
worktree).
