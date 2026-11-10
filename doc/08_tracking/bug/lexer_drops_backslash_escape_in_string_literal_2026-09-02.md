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

## Addendum 2026-11-11 — P3 lane compiler3 verdict: LIVE — FIXED in seed lexer (commit a8a1070724d7)

Triage on refreshed seed (build-commit 0791c2b7f4a7, bin/simple.exe 37577216 bytes)
at release/1.0.0 tip 7d4140c1a6b3 (work/p3-compiler3-20261111).

- LIVE confirmed: byte-level probe on the refreshed seed measured raw `"a\b"`
  → `a`+0x08 (len 2), `"C:\Temp"` → len 6, `"C:\Windows\System32"` → len 17 —
  backslashes deleted exactly as filed.
- Root cause (measured, not inferred): the seed lexer
  (`src/compiler_rust/parser/src/lexer/escapes.rs process_escape`) dropped the
  backslash in its default arm (`\T` → `T`), and had non-authority arms
  (`\b`→backspace, `\a`/`\f`/`\v`, `\:`/`\/`/`\.`/`\-`) that the pure-Simple
  lexer (`lexer_struct.spl scan_string`, the semantic authority) does not have —
  its `else` preserves `\` + char for every non-escape.
- Fix (a8a1070724d7): new `EscapeResult::KeepBoth(char)` — unknown escapes keep
  both bytes at all four call sites (f-string, ADR-005 char literal, i18n x2);
  the non-authority arms were removed; `\{`/`\}` intentionally retained
  (load-bearing JSON/CSS spec users — a residual divergence from the authority,
  recorded here as follow-up).
- Verification (seed-smoke labels throughout):
  - `cargo test -p simple-parser` → 453 passed + 2 new pinning tests
    (`test_unknown_escape_preserves_backslash`,
    `test_unknown_escape_in_char_literal_is_error`), 0 failed.
  - End-to-end on a debug seed rebuilt from this tree (cargo build, llvm-mingw
    clang shim; NOT the tracked bin/simple.exe): probe spec 5/5 — raw
    `"a\b"` len 3, `"C:\Temp"` len 7, `"C:\Windows\System32"` len 19 (byte
    inspection: both backslashes present), escaped `"a\\b"` len 3,
    `char_from_code(92)` oracle len 3.
  - Regression spot-checks (fixed vs unfixed seed, identical results):
    `string_literals_spec.spl` 24/24 PASS both; `json_unicode_escape_spec.spl`
    6/11 both (5 pre-existing failures); `query_diagnostics_spec.spl` 11/15
    both (4 pre-existing failures, `\{` behavior unchanged).
- Correction to this doc: the expected length table's "20" for
  `C:\Windows\System32` is a miscount — the literal is 19 characters
  (C, :, \, W…s, \, S…2). The pre-fix JIT measurement of 19 was actually
  correct; only the interpreter's 17 was the defect.
- Note: the tracked refreshed seed bin/simple.exe does NOT contain the fix
  (seed rebuild needed); the end-to-end evidence above comes from a debug build
  of the same source tree. The pure-Simple self-hosted side needed no change —
  it already implements the preserving contract.
