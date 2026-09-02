# Lint rule: `windows_portability` — PATH-WIN-001 / EOL-CRLF-001

- **Added:** 2026-09-02
- **Severity:** WARNING (both codes). Not wired into any blocking gate.
- **Implementation:** `src/compiler/35.semantics/lint/windows_portability.spl`
- **Wiring:** `src/compiler/90.tools/lint/_LintMain/lint_checks.spl`
  (`check_windows_portability`), code→rule-name map in
  `_LintMain/config_and_model.spl`
- **Specs:** `test/01_unit/compiler/lint/windows_path_literal_spec.spl`,
  `test/01_unit/compiler/lint/windows_portability_negative_controls_spec.spl`
- **Push-time twin:** `scripts/check/check-no-windows-style-paths.shs`

## Policy

> *"code should not have `c:\` style path. only mingw / linux style, and lib
> path/file convert it for system."* — user, 2026-09-02
>
> *"lint windows style newline in spl shs sdn."*

Product code carries only MinGW/POSIX path form (`/c/Users/...`). The native
`c:\Users\...` spelling belongs exclusively to the library boundary layer whose
job is producing it. Line endings are LF everywhere except `.cmd`/`.bat`, which
genuinely require CRLF because cmd.exe misparses LF-only batch files.

## Codes

| code | shape | severity |
|---|---|---|
| `PATH-WIN-001` | a drive letter, a colon, then a backslash — `c:\`, `D:\tmp` | warning |
| `EOL-CRLF-001` | file uses CRLF line endings; one finding per file, at the first CR-terminated line | warning |

Numbering follows the `PERF-COW-00x` family: a per-code suffix inside one named
rule, so `simple.sdn` can set a level for the rule as a whole.

## Scope

`.spl`, `.shs`, `.sdn` only. `.cmd`/`.bat` are excluded from **both** codes.
Vendored trees (`*/vendor/*`, `*/node_modules/*`, `miniaudio.h`, `stb_image.h`,
`stb_truetype.h`) are excluded per CLAUDE.md Owned-Code Scope.

`.shs` and `.sdn` coverage is the novel part of this rule: no AST-based lint can
see a shell script or a data file, so detection is a line-based text pass.

## Detection semantics

Deliberately identical to the ratchet's ERE `[A-Za-z]:\\` plus a trailing-CR
test, so the authoring-time rule and the push-time guard cannot drift. The
ratchet's negative controls are the rule's, and are pinned by the second spec:

| input | verdict |
|---|---|
| `/c/Users/ormas` (MinGW form) | clean — no colon before a separator |
| `"C:"` (bare drive mention) | clean — no backslash follows |
| `weird\name.txt` (legal POSIX filename) | clean — no drive-letter + colon prefix |
| an LF file | clean — never reported as CRLF |

### Cross-platform impact

The linter runs on Unix, where a backslash is an **ordinary** filename
character. The third row above is load-bearing: flagging a bare backslash would
make the linter unusable on POSIX. Nothing in the rule inspects the host
platform or rewrites separators, so the verdict for a given byte sequence is
identical on every OS.

### Why EOL-CRLF-001 reads raw bytes

`file_read` normalizes CRLF to LF before any lint rule sees text — measured
2026-09-02: a 6-byte `a\r\nb\r\n` file reads back as 4 characters with zero CRs.
A rule working from the linter's `content` therefore cannot see CR at all. The
wrapper in `lint_checks.spl` calls `file_read_bytes(path)` and hands the raw
bytes to the pure function `check_windows_line_endings_bytes`.

One finding per file, not per line: a converted 2,000-line file would otherwise
contribute 2,000 warnings and drown every other rule. The message carries the
total CRLF line count.

### Implementation hazard: the lexer drops `\`

`"C:\\Users"` lexes to `C:Users` on this compiler — see
`doc/08_tracking/bug/lexer_drops_backslash_escape_in_string_literal_2026-09-02.md`.
Every character the rule matches on is built with `char_from_code`
(`winport_backslash()` = 92, `winport_cr()` = 13), never as a literal escape.
The specs **assert byte length** (`winport_backslash().len() == 1`) rather than
appearance, so a pattern that silently collapsed to the empty string fails
loudly instead of matching nothing and reporting clean.

## Suppression

Four mechanisms, in increasing breadth:

1. **Per line** — a trailing `# lint-allow: PATH-WIN-001` comment. Use for
   regex/pattern text where the backslash is a metacharacter.
2. **Per file** — the same marker anywhere in the file suppresses that code for
   the whole file. Use for a spec that deliberately asserts `/d/foo` → `d:\foo`,
   or a fixture that must be CRLF.
3. **Per file, automatic** — the conversion layer. A file that defines
   `to_native_path`, `to_backslash`, or `_msys_drive_path`, or is named
   `host_path.spl`, is never flagged by `PATH-WIN-001`: producing native paths
   is its job. This mirrors the allowlisted-provider precedent in
   `check-no-direct-rt.shs`.
4. **Per project** — `[lints] windows_portability = "off"` in `simple.sdn`, via
   the code→rule-name mapping in `_LintMain/config_and_model.spl`.

## Existing debt

Measured 2026-09-02 across the tree: **439** `.spl` offender files of 42,611,
**75** `.shs` of 2,308, **0** `.sdn` of 1,096 — 514 files in total.

Handled by severity alone: both codes are WARNING, never Deny, so `lint` still
exits 0 and the existing population cannot block anyone. No baseline or
allowlist file was created — the conversion-layer exemption removes the only
*legitimate* offenders, and the remainder is real debt that should stay visible.
The precedent (`PERF-COW-00x`, `RAW-RT-00x`, `LEADOP001`) is that a rule is not
escalated before its population is converted. Neither code is wired into any
blocking gate.

## Verified by execution (2026-09-02)

Seed `bin/simple.exe`, md5 `d52d770724a9f8797e98ac7819709ab9`. Exit status read
directly into a variable, never through a pipe.

```
$ bin/simple.exe lint build/lintfix/pos_path.spl        # rc=0
build/lintfix/pos_path.spl:2:0: warning[PATH-WIN-001]: Windows-style native path literal (drive letter + colon + backslash)
Lint passed: 0 error(s), 1 warning(s) in 1 file(s)

$ bin/simple.exe lint build/lintfix/neg_path.spl        # rc=0
Lint passed: all files clean

$ bin/simple.exe lint build/lintfix/pos_crlf.spl        # rc=0
build/lintfix/pos_crlf.spl:1:0: warning[EOL-CRLF-001]: Windows (CRLF) line endings — 2 line(s); .spl/.shs/.sdn must be LF

$ bin/simple.exe lint build/lintfix/neg_crlf.spl        # rc=0
Lint passed: all files clean

$ bin/simple.exe lint build/lintfix/pos_path.shs        # rc=0
build/lintfix/pos_path.shs:1:0: warning[PATH-WIN-001]: ...

$ bin/simple.exe lint build/lintfix/pos_path.sdn        # rc=0
build/lintfix/pos_path.sdn:1:0: warning[PATH-WIN-001]: ...

$ bin/simple.exe lint build/lintfix/neg_path.sdn        # rc=0
Lint passed: all files clean
```

Fixtures were written byte-exactly (verified: `pos_path.spl` 50 bytes with 2
backslashes; `pos_crlf.spl` 25 bytes with 2 CRs) precisely because the lexer
hazard above makes an eyeballed fixture untrustworthy.

Specs: 17 cases, 17 passing.
