# Co-compiled duplicate definitions with differing signatures — dispatch class

Status: FIXED — verified 2026-11-11 (lane ne4); raw-wrapper rename landed 2026-11-08 (fe8c1a623557) and resolver is fail-closed (10e216d19f8c)
Found: 2026-08-31, while fixing known_bugs C12/C13.

Resolution: the five remaining raw/high-level collisions (`atomic_bool_new`,
`env_get`, `env_vars`, `process_run_with_limits`, and `process_wait`) now use
unique `sffi_`-prefixed raw names. Re-export facades and every caller across
`src`, including the MIR lowering caller, are migrated; unset environment
values retain their `?? ""` behavior. `atomic_i64_new`,
`mcdc_condition_key`, and `shell` were already fixed and are unchanged.
`raw_high_level_duplicate_signature_spec.spl` statically pins all eight pairs
as absent and forbids bare facade re-exports. The Simple spec was not executed
in this lane, so runtime verification remains pending.

## Symptom

Every `bin/simple test` run emits a family of warnings:

```
warning: public function `NAME` has N co-compiled definitions with 2 differing
signatures (SIG_A vs SIG_B); JIT call sites resolve by exact arg-type match
(mangled `$dupN` variants), falling back to the last definition when types are
ambiguous — a fallback hit may still dispatch to the wrong one.
[compiler_cross_module_private_symbol_collision]
```

Observed symbols and signature pairs:

| symbol | signatures |
|---|---|
| `atomic_bool_new` | `(bool)->AtomicBool` vs `(bool)->bool` |
| `atomic_i64_new` | `(i64)->AtomicI64` vs `(i64)->i64` |
| `env_get` | `(text)->Optional(text)` vs `(text)->text` |
| `env_vars` | `()->Optional([(text,text)])` vs `()->[(text,text)]` |
| `mcdc_condition_key` | `(McdcConditionResult)->text` vs `(text,i64)->text` |
| `process_run_with_limits` | `(text,[text],i64,i64)->(text,text,i32)` vs `(text,[text],i64,i64,i64,i64,i64)->ProcessResult` |
| `process_wait` | `(i64)->i64` vs `(i64,i64)->i64` |
| `shell` | `(text)->ProcessResult` vs `(text)->i64` |

The recurring shape is a low-level raw SFFI wrapper in
`src/lib/nogc_sync_mut/sffi/*.spl` sharing a bare name with the higher-level
`src/lib/nogc_sync_mut/io/*.spl` API. Example pair:

- `src/lib/nogc_sync_mut/sffi/system.spl:189` `fn process_run_with_limits(cmd, args, timeout_ms, memory_bytes) -> (text, text, i32)`
- `src/lib/nogc_sync_mut/io/process_ops.spl:547` `pub fn process_run_with_limits(cmd, args, timeout_ms, memory_bytes, cpu_seconds, max_fds, max_procs) -> ProcessResult`

## Why it is recorded rather than fixed here

The warning itself is honest and the fallback is only *potentially* wrong; no
spec in this batch was shown to mis-dispatch because of it. Both bugs it was
hypothesised to explain turned out to have unrelated root causes:

- C13 (`process_run_with_limits` empty stdout) was a shell-quoting defect in
  `_process_run_with_limits`, not dispatch. Fixed.
- C12 (`try_recv` / `join` nil) was the non-optional return contract, not
  dispatch. Partially fixed.

The durable fix is either renaming the sffi-side raw wrappers to unique names
(mechanical but touches many call sites across `src/lib` and `src/app`), or
making the JIT resolver fail closed instead of falling back to the last
definition. Both are larger than a smallest-correct-change bugfix and the
second is a compiler design decision.

## Suggested next step

Rename the raw wrappers in `src/lib/nogc_sync_mut/sffi/` with an `sffi_`
prefix (`sffi_process_run_with_limits`, `sffi_env_get`, `sffi_shell`, ...) so
the warning class goes to zero, then make the diagnostic fatal to keep it there.

## 2026-11-11 addendum (lane ne4, batch p3-ne4-20261111)

Verdict: FIXED (pending -> fixed). Both halves of the suggested durable
fix are landed on release/1.0.0 (worktree tip fa6366ca8bf5):

1. `fe8c1a623557` "fix(sffi): deduplicate raw wrapper names" (2026-11-08)
   — the five live raw/high-level collisions now use unique `sffi_`
   names (`sffi_atomic_bool_new`, `sffi_env_get`, `sffi_env_vars`,
   `sffi_process_run_with_limits`, `sffi_process_wait`); facades and
   callers migrated. `atomic_i64_new`, `mcdc_condition_key`, `shell`
   unchanged as documented.
2. `10e216d19f8c` "fix(resolve): ambiguous co-compiled duplicate
   definition is a compile error (owner decision 6)" (2026-11-09) —
   the JIT/HIR/MIR resolver no longer falls back to the last definition
   for ambiguous bare-name dispatch; it fails closed. Repro:
   `test/01_unit/compiler/interpreter/ambiguous_co_compiled_fn_call_error_spec.spl`.

Runtime verification that was pending is now done (seed-smoke, refreshed
2026-11-11 seed, build-commit 0791c2b7f4a7):
`test/01_unit/lib/nogc_sync_mut/sffi/raw_high_level_duplicate_signature_spec.spl`
(the pinning spec named in this doc) -> 4/4 PASS. The compile of the
full sffi/io surface during that run emits no
`compiler_cross_module_private_symbol_collision` warnings for any of the
eight historical pairs.
