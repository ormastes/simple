# `rv64_compliance_spec.spl` imports modules that don't exist in `src/lib/hardware/rv64gc`

- **Date:** 2026-07-20
- **Status:** open
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
