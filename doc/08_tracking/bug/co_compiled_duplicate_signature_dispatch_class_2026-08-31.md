# Co-compiled duplicate definitions with differing signatures — dispatch class

Status: OPEN (recorded, not fixed)
Found: 2026-08-31, while fixing known_bugs C12/C13.

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
