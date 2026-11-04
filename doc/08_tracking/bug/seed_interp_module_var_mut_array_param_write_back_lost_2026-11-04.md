# Seed interpreter: module-scope call drops `mut` array-param writes into a module `var`

- **Filed:** 2026-11-04 (modvar lane), split out of
  `seed_interp_mut_u8_array_param_element_write_lost_2026-11-04.md`.
- **Status:** FIXED in source (this lane); seed redeploy is the bootstrap lane's.
- **Platform:** aarch64-apple-darwin (mechanism is platform-independent).

## Minimal repro

```simple
var gi: [i64] = [0; 4]
fn set(mut a: [i64]):
    a[0] = 7
set(gi)
print "gi0={gi[0]}"
```

| seed | `simple run` | `SIMPLE_EXECUTION_MODE=interpreter` |
|---|---|---|
| before | `gi0=0` | `gi0=0` |
| after | `gi0=7` | `gi0=7` |

Same for `[u8]`, `[f64]`, call depth 2, and a struct-held array (`set(h.data)`).

Scope correction vs the parent doc's note: the gap is the **call site at module
scope**, not "module var" in general. The same module `var` passed from inside
`main()` (or any function body) already wrote back in both modes. There is also
no separate JIT defect: a file whose module-level statements do the work has no
`main`, so `simple run` prints `[engine-demotion] reason=jit-bail:no-main-fn` and
runs the interpreter — the "JIT" failure was this interpreter path.

## Root cause

`write_back_mutable_arguments` (`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`)
wrote the callee's final value only into the calling frame (`outer_env.insert`).
At module scope, identifier reads resolve through the module-global stores
(`MODULE_GLOBALS` / owner store), which were never updated, so the caller kept
reading the pre-call array. Index/field place writes already mirror through
`place::sync_module_global`; the Bug #19 write-back did not.

## Fix

After the identifier and one-level-field write-back inserts, call
`place::sync_module_global` (now `pub(crate)`) for the caller binding unless it is
a frame-local (so a local shadowing a global name never clobbers the global).

## Evidence

- `cargo test --release --test interpreter_module_var_mut_array_param_write_back` — 3/3;
  sibling `interpreter_mut_u8_array_param_write_back` — 2/2.
- `test/01_unit/compiler/interpreter/module_var_mut_array_param_write_spec.spl`:
  worktree seed 6/6 under both `simple run` and `simple test`; pre-fix seed 0/6.

## Noted, not fixed here

With a `main()` defined, `simple run` (JIT) executes `main` but silently skips
module-level statements that follow the `main()` call (the interpreter runs them).
Separate behaviour; not this defect.
