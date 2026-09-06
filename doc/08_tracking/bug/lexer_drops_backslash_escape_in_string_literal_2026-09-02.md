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

## Correction + widening, measured 2026-09-02 (windows-path `.spl` lane)

(Re-applied: a parallel session restored this file over these findings once
already. Same host and binary, md5 `d52d770724a9f8797e98ac7819709ab9`.)
All figures are BYTE LENGTHS via `.len()`, never appearance — the assertion
formatter itself mangles backslashes, so a printed value proves nothing.

**1. The escaped form `\` is NOT uniformly broken.** The report above concerns a
SINGLE backslash, and that half reproduces exactly (`"C:\Users\ormas".len()`
measures 12, not 14; `"a\b".len()` measures 2). An author-escaped `\` mostly
works, so the widely-repeated restatement "the lexer silently drops `\`" is
false and must not be used to justify a rewrite.

**2. The two engines DISAGREE — contradicting "Same result under both engines".**

| literal | expected | `run` (JIT) | `test` (interpreter) |
|---|---|---|---|
| `"a\b"` | 3 | **3** | **2** |
| `"C:\Temp"` | 7 | **7** | **6** |
| `"C:\Windows\System32"` | 20 | **19** | **17** |
| `"C:\a\b.txt"` | 10 | 10 | 10 |
| `"C:\Users\ormas"` | 14 | 14 | — |
| `"C:\simple"` / `"C:\windows"` / `"C:\LLVM\bin\clang-cl"` / `"C:\Simple\simple.exe"` / `"C:\MissingDir"` | 9/10/20/20/13 | — | all correct |

The loss is engine-specific AND content-dependent. A positional rule of thumb
("embedded `\` is dropped, trailing is fine") does not survive
`"C:\a\b.txt"`, correct at 10 on both. On `"C:\Windows\System32"` — the
literal that was live in `src/compiler/70.backend/linker/link_deps.spl:159-160`
— **both** engines are wrong, by different amounts, so neither can serve as an
oracle for the other.

**3. Consequences.** `"C:\Temp"` was live product code in `_get_temp_dir`'s
Windows fallback and measured 6 bytes under the engine that runs the test suite.
Those sites have since been converted to forward-slash form, which sidesteps the
defect entirely.

**4. Writing a regression spec here.** Do not build a backslash from an escaped
literal. Two engine-independent routes exist: `char_from_code(92)` (used by
`test/01_unit/lib/common/windows_path_*_spec.spl`), and a RAW string —
`r"C:\Users\name"` — which `test/01_unit/lib/common/string_literals_spec.spl:68`
already relies on and which is unaffected by this defect.
