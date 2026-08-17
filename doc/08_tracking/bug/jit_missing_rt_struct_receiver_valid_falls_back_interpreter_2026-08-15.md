# JIT lane reports missing runtime fn `rt_struct_receiver_valid` and silently falls back to interpreter

- **Date:** 2026-08-15
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  session in `f11bd8f0d6b` "fix(jit): register struct-field runtime funcs"
  (runtime_sffi.rs RuntimeFuncSpec for rt_struct_alloc +
  rt_struct_receiver_valid). Post-lock verification: the repro below must run
  JIT without the missing-fn message.
- **Area:** src/compiler_rust JIT runtime-symbol registration
- **Severity:** perf/coverage — programs silently demote to the tree-walk interpreter

## Symptom

Observed 2026-08-15 while running engine2d specs on the freshly rebuilt seed:
the JIT lane fails with `missing runtime fn 'rt_struct_receiver_valid'` and the
program falls back to the interpreter. Per `.claude/rules/testing.md`, a single
unsupported operation demotes the WHOLE program — so any `bin/simple run`
workload touching this symbol is silently interpreter-speed, and JIT-vs-
interpreter A/B results are contaminated.

## Suspected cause

`rt_struct_receiver_valid` is referenced by JIT codegen but not registered in
the JIT's runtime symbol table (check `src/compiler_rust/common/src/
runtime_symbols.rs` — recently modified in-tree — and the JIT builtin
registration path). Likely an extern added for the interpreter without the
matching JIT symbol entry.

## Wanted

Register the symbol for the JIT (or remove the codegen reference), plus a test
that greps/probes for silent JIT→interpreter demotion on a minimal class-method
program so this class of regression fails loudly.

Verification blocked at filing time by the repo-wide bootstrap resource lock.
Repro after lock: `SIMPLE_EXECUTION_MODE=jit bin/simple run <minimal class
program>` and check stderr for the missing-fn message.
