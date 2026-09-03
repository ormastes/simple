# Lexer DROPS `\` in a string literal instead of emitting one backslash

- **Filed:** 2026-09-02 — found while reproducing
  `is_dir_always_false_shell_dependency_2026-09-02.md`
- **Status:** OPEN (compiler defect; not fixed here)
- **Host:** Windows 11, `bin/simple.exe` 16,347,136 bytes,
  md5 `d52d770724a9f8797e98ac7819709ab9`

## Symptom

```
val p = "C:\Users\ormas\dev\simple"
print("[{p}] len={p.len()}")
```

prints `[C:Usersormasdevsimple] len=21`. Expected `[C:\Users\ormas\dev\simple]`
with `len=25`. Each `\` is **deleted entirely** rather than collapsing to one
backslash. Same result under both engines (`run`/JIT and `test`/interpreter).
`"bin\bb"` → `binb`, len 5.

## Why it matters beyond aesthetics

It makes every literal-backslash test fixture **silently vacuous**. The original
`is_dir` bug report recorded "`is_dir` fails for any backslash path even under
JIT". That observation was produced by exactly this literal, so it was never
testing a backslash path at all — it was testing `C:Usersormasdevsimple`, which
correctly is not a directory. A path predicate can therefore be "proven broken"
or "proven fixed" on Windows by a fixture that contains no separators.

## Evidence that `is_dir` itself is fine

Constructing a genuine backslash at runtime — recovered from
`dir_walk_native`, which joins with the platform separator, via
`sample.substring(sample.len() - 3, sample.len() - 2)` on a known 2-char leaf —
gives `is_dir(bwd) = true` for the repo root and `false` for a file under it, in
**both** engines. So the runtime and the filesystem layer handle backslashes
correctly; only the lexer is wrong.

## Repro harness

Any two-line program with a `\` in a literal reproduces it. A regression spec
must not use a literal backslash to assert this — it should assert
`"a\b".len() == 3`, which fails today (measured: 2 after the drop... verify the
exact count when fixing, the observed rule is deletion of the whole pair).

## Cross-platform note

This is a lexer/escape-processing defect, not path handling. Fixing it must not
introduce any separator rewriting: a backslash is a legal character in a POSIX
filename, and `\` must mean exactly one literal backslash on every platform.
POSIX was **not** testable on this host.

## Unblock / owner

Lives in the escape-processing path of the Simple lexer
(`src/compiler/10.frontend/**` and its seed counterpart in
`src/compiler_rust/`). Needs a seed rebuild to verify the seed-side half.
