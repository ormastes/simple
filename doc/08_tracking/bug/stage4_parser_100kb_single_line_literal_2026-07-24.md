# Stage-4 self-hosted parser fails on >100KB single-line string literals — scale-dependent, not a syntax defect

**Date:** 2026-07-24
**Severity:** high (blocked stage-4 full-CLI build)
**Status:** worked around (line split in the one file that hit it); root
cause in the self-hosted lexer/parser is unfixed
**Found by:** stage-4 full-CLI build triage (stage2 self-hosted parser, deep
into the build with the module/heap registry around ~45.8M entries)

## Symptom

Building the full CLI with the stage-2 self-hosted parser failed with:

```
[parser_error] path src/app/ui.web/html.spl line 118:104550: expected :, got StringLit
```

`src/app/ui.web/html.spl` line 118 was a single `html = html + "..."`
statement whose string literal was 109,477 characters long (one giant
escaped-HTML blob for the `wm-quality-inspector` `<aside>` markup).

## Scale-dependence evidence

- **Isolated parse: OK.** Copying the file alone into a scratch dir and
  running it through the exact same stage-2 binary
  (`build/bootstrap/stage2/aarch64-apple-darwin/simple`) via `native-build`
  parses and compiles the file cleanly (produces a linked binary, only the
  expected "unresolved symbol" stubs for cross-module functions it doesn't
  have visibility into standalone). `bin/simple check
  src/app/ui.web/html.spl` in-repo also parses cleanly (only unrelated
  `rt_process_spawn_guarded` extern-resolution noise, not a parse error).
- **In full-CLI-build context: fails**, specifically only once the parser's
  internal heap/registry state has grown to roughly 45.8M entries from
  everything parsed before this file in module order.

This rules out a literal-content/escaping bug in the string itself (same
bytes, same lexer, two different outcomes depending on how much state has
accumulated in the process). It points at a scale-dependent defect in the
self-hosted lexer/parser's handling of very long single-line string
literals — plausibly an internal buffer/offset field that overflows or
wraps once combined with a large pre-existing heap/arena, given the error
column (`104550`) lands well inside the string body rather than at a real
token boundary. Not root-caused further here; flagging for lexer/parser
owners.

## Workaround applied

Split the single 109,477-char literal in
`src/app/ui.web/html.spl` line 118 into 28 consecutive statements of the
same form:

```simple
    html = html + "<chunk of the original string, unmodified bytes>"
    html = html + "<next chunk>"
    ...
```

- Each chunk's line length (prefix `    html = html + "` + payload + `"`)
  is ≤ 4,000 characters.
- Split points are always immediately **after** a literal `>` character in
  plain HTML text, never between a backslash and the character it escapes,
  so no escape sequence (`\"`, `\\`, `\n`) is ever broken across chunks.
- Concatenating the 28 new payloads reproduces the original 109,457-byte
  payload byte-for-byte (verified independently, see below).

The file grew from 2,341 to 2,368 lines (net +27 lines, 118 → 118-145);
lines 1-117 and the old 119-end (now 146-end) are untouched.

## Verification performed

1. **Byte-equivalence** — independent script (not reusing the split
   script's own internal check) extracted the prefix/suffix-stripped
   payload from the backed-up original line 118 and from the 28 new lines,
   concatenated the new payloads, and byte-compared:
   ```
   orig payload bytes: 109457
   new  payload bytes: 109457
   BYTE-EQUIVALENCE: PASS (identical)
   ```
2. **`bin/simple check src/app/ui.web/html.spl`** — no parse error (only
   the pre-existing, unrelated `unknown extern function:
   rt_process_spawn_guarded` semantic-check message).
3. **Isolated stage-2 native-build parse** of the edited file (copied to a
   scratch dir as `f.spl`), via
   `build/bootstrap/stage2/aarch64-apple-darwin/simple native-build
   --target aarch64-apple-darwin --backend cranelift --runtime-bundle
   core-c-bootstrap` — succeeded, no parse error, produced a linked
   `out.bin` (50 KB) with only the expected cross-module unresolved-symbol
   stubs.

## Repo-wide sweep for the same class of landmine

Scanned every `.spl` file under `src/` and `examples/10_tooling/` for
lines over the danger thresholds (`git ls-files 'src/*.spl'
'examples/10_tooling/*.spl'`, ~13,725 files):

- **>100,000 chars:** none remaining (the one instance, `html.spl` line
  118, is the one fixed above).
- **50,000-100,000 chars (at-risk, not touched):** none found.
- For reference, the single largest remaining line anywhere in that sweep
  is `src/os/desktop/modern_wm_readiness.spl:508` at 12,710 chars — well
  under both danger bands, left as-is.

## Root cause status

**Unfixed.** This doc records a targeted workaround for the one file that
actually broke the stage-4 build, plus confirmation nothing else in-tree
currently sits in the >100KB or 50-100KB bands. The underlying
scale-dependent lexer/parser defect (long single-line string literals
failing only once a large amount of prior state has accumulated in the
same process) is not root-caused and will resurface if a future file
introduces another giant single-line literal, or if the state threshold at
which it triggers turns out to be lower than 45.8M heap entries for
different workloads.

## Affected

- `src/app/ui.web/html.spl` — line 118 split into 28 lines (now spans
  118-145).
