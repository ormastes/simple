# `simple lint <directory>` SEGVs in the JIT lane, prints nothing, dumps core

- **Filed:** 2026-09-12
- Status: OPEN (2026-09-12)
- **Found by:** L5-D (generated/deployed binary closure wave), while pinning
  `simple check <dir>` directory-recursion membership.
- **Binary:** deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`,
  51,308,600 B, sha256
  `3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`.
  Tree: `c7c5bef3ca3` (Merge pull request #568), unmodified.

## Symptom

Given a directory target, `simple lint` dies with SIGSEGV before emitting a
single byte on stdout. `simple lint <one file>` on the same tree is fine, and
`simple check <the same directory>` is fine, so it is specific to lint's
directory path.

## Reproducer

The fixture ships with this repo (added by L5-D for the `check` membership pin);
it is five `.spl` files at three depths plus one non-`.spl` sibling:

```sh
cd <repo root>
bin/release/aarch64-unknown-linux-gnu/simple lint test/fixtures/app/check/membership
echo "rc=$?"
```

Observed, reproduced on consecutive runs and with `SIMPLE_JIT_STRICT=1` set:

```
rc=139
Segmentation fault (core dumped)
```

stdout is **0 bytes**. stderr carries only the usual `export use *` lint
warnings and the `compiler_cross_module_private_symbol_collision` warnings
(`env_get`, `env_vars`, `join_path`, `process_run_with_limits`, `process_wait`,
`shell`), then the process dies.

## The crash is in JIT-compiled code

Same binary, same tree, same command, interpreter lane:

```sh
SIMPLE_EXECUTION_MODE=interpreter \
  bin/release/aarch64-unknown-linux-gnu/simple lint test/fixtures/app/check/membership
echo "rc=$?"
```

```
rc=0

Lint passed: all files clean
```

So the work itself is correct — discovery finds the five files, linting passes —
and only the JIT lane faults. `SIMPLE_JIT_STRICT=1` does **not** change the
outcome, which rules out a fallback-path interaction: the strict flag turns a
*deferred* module into a hard error, and here nothing is deferred, the compiled
code simply faults.

## Why this was not noticed before

It is invisible in the two places a user would look. `simple lint <file>` — the
overwhelmingly common invocation and the one the `lint-one-file` closure entry
uses — never touches the faulting path. And a spec runner run exports
`SIMPLE_EXECUTION_MODE`, so every spec that shells out to `simple lint <dir>`
takes the interpreter lane and passes.

## Scope note, so this is not mis-scoped on pickup

This was found while measuring import closures, and a closure change *does*
change the symptom — leaf-importing `src/app/cli/lint_entry.spl` makes the crash
disappear. That is not a fix and must not be recorded as one: it works only
because the leaf import causes the whole lint program to stop JIT-compiling at
all (see
`doc/08_tracking/bug/jit_unresolved_aliased_import_drops_whole_module_2026-09-12.md`),
i.e. it silently moves every lint invocation onto the interpreter. The defect
here is in the JIT-compiled lint directory path and is independent of any import
layout.

## Not yet determined

- Which frame faults. No core-file analysis has been done; `ptrace_scope=1` and
  `perf_event_paranoid=4` on this host block attach-based profiling
  (see `.claude/rules/commands.md`).
- Whether the fault needs the *recursive* walk specifically. The fixture is
  mixed-depth (depth 0, 1 and 2); a flat single-directory target has not been
  tried in isolation.
- Whether it reproduces on x86_64. Measured on aarch64 only.
