# Native advice-classifier evidence

Requirements: REQ-ADVICE-SCAN-001/002/003.
Executable: `test/fixtures/compiler/advice_lexical_scan/main.spl`.
Production owner: `compiler.driver.driver_advice_scan_v1`.

The standalone native fixture calls the real scanner 21 times and prints each
assertion verdict. Its exit status is the failure count; a missing scanner
source file exits 99, never PASS. The source-self-check reads the actual helper
file, which contains the candidate marker only in its string literal.

Coverage: real advice; tab whitespace; indentation; UTF8 preceding comment;
ordinary identifiers; line/inline comments; double/single/raw/triple-double/
triple-single/raw-triple strings; escaped quote; identifier boundary; missing
whitespace; newline separation; space before brace; intervening comment;
conservative lexical error; scanner's own source.

Observed under immutable self-hosted Stage2 43f9a6fc… and matched runtime:

| Version | Executed assertions | Failures | Native exit |
|---|---:|---:|---:|
| Original substring predicate | 21 | 14 | 14 |
| Streaming CoreLexer classifier | 21 | 0 | 0 |

Compile with `native-build --backend cranelift --runtime-bundle host-gpu
--runtime-path <matched-capsule> --source src/compiler --source src/lib
--entry-closure --entry test/fixtures/compiler/advice_lexical_scan/main.spl
--threads 4 --cache-dir <private-native-cache> --output <owned-executable>`.
Use the canonical process-group timeout/RSS owner with explicit private
frontend/HIR/native caches. The verified focused diagnostic selected
`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`, `SIMPLE_UNIT_TLDR_IMPORTS=0` and
`SIMPLE_TLDR_IMPORTS=0`, preserving AOP and enforcement. The test run pinned
`SIMPLE_CHAR_LITERAL_LEXER=0` for the supported legacy single-quoted-string
cases. Run the executable from the source worktree root.

Raw build/run logs and watchdog receipts are in the owning session's
`build/advice-scan/{before,after}`. See the linked bug record by filename
`worker_advice_lexical_false_roots_2026-11-06.md` for identities and failed
attempts. This manual reports native fixture evidence, not an SSpec-runner
PASS or complete compiler/Phase-3 qualification.
