# `bin/simple lint` aborts: `class CodeLine has no field named code`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-06
**Status:** FIXED (2026-11-11, lane ne14) — fixing commit eea2a322ac74; verified on release/1.0.0 tip, see addendum
**Severity:** High for tooling — the linter cannot complete on affected files,
so `bin/simple lint <changed files>` (a `.claude/rules/commands.md` step) is
unreliable.
**Component:** `src/compiler/35.semantics/lint/linear_scan_in_loop.spl`

## Symptom

```
$ bin/simple lint src/app/devhub/retry.spl
error: semantic: class `CodeLine` has no field named `code`
```

The process still exits **0**, so a caller checking only the exit status reads
this as a pass. There is no verdict line and no findings are reported: the file
was not linted at all.

## Reproduction

Reproduces on an untouched, committed file and on a two-line fixture:

```bash
bin/simple lint src/app/devhub/retry.spl          # error
printf 'fn f() -> i64:\n    1\n' > /tmp/tiny.spl
bin/simple lint /tmp/tiny.spl                     # error
```

Not universal — `bin/simple lint src/app/devhub/adapter_github.spl` and
`src/app/devhub/backend_resolve.spl` both complete normally
(`Lint passed: all files clean`), so the abort depends on which rules a given
file drives, not on file size or complexity. A 20-line head of the same
`retry.spl` that errors does **not** error, which rules out "large/complex file".

## Cause (located, single line)

`src/compiler/35.semantics/lint/linear_scan_in_loop.spl:84`

```simple
for cl in snapshot.lines:
    val raw = cl.raw
    val code = cl.code        # <-- CodeLine has no `code` field
```

`CodeLine` (`src/compiler/35.semantics/lint/lint_text.spl:10-13`) declares
exactly three fields:

```simple
class CodeLine:
    line_num: i64
    raw: text
    trimmed: text
```

So `PERF-SCAN-001` (`check_linear_scan_in_loop_snapshot`) has **never** been
able to run: it fails semantic analysis the moment it is reached, and takes the
whole lint invocation down with it.

## Proposed fix

`cl.code` -> `cl.trimmed`. The surrounding code corroborates that this is the
intent: `raw` is bound separately and used only for `line_indent(raw)`, while
`code` is used exclusively as `code.trim()` for prefix tests — which is what
`trimmed` already is, making `.trim()` on it idempotent and harmless.

## Why this was not fixed in passing

The fix is one token, but landing it does more than repair a crash: it **turns
on a lint rule that has never executed**, across ~14k `.spl` files. `PERF-SCAN-001`
flags whole-container scans inside a loop, a pattern that is certain to be
widespread in a codebase that has never been checked for it. That is a
ratchet-population decision (new findings, possibly a new baseline, possibly
broken lint gates in other lanes), not a drive-by repair, and it belongs to
whoever owns the lint ratchet rather than to an unrelated feature change.

Discovered while running the mandated `bin/simple lint` step on
`src/app/devhub/gh_compat.spl` for the devhub `gh`-shim change; that change is
unrelated to this defect and does not touch `src/compiler/`.

## Suggested next step for the owner

1. Apply `cl.code` -> `cl.trimmed`.
2. Run `bin/simple lint` over a representative sample to size the new finding
   population before enabling it broadly.
3. Add a spec that lints a fixture containing a whole-container scan inside a
   loop and asserts `PERF-SCAN-001` is reported — the rule currently has no
   coverage, which is why a field name that never existed went unnoticed.
4. Separately: make the linter exit non-zero when it aborts. A run that
   analysed nothing must not exit 0 (same principle the pre-push guards apply —
   `ERROR — nothing was checked` is exit 2, never a pass).


## Addendum 2026-11-11 (lane ne14) — FIXED, verified on release/1.0.0

**Fixing commit:** `eea2a322ac74` "fix(lint): read CodeLine.trimmed in
linear_scan_in_loop" (2026-10-09). The rule now reads `cl.trimmed` (line 219);
no `.code` reference remains anywhere in
`src/compiler/35.semantics/lint/linear_scan_in_loop.spl`. A spec case was added
by the same commit.

**Verification actually run** (seed-smoke, worktree simple-p3-ne14-20261111,
fresh seed 46fe8f6b6def, SIMPLE_LIB=src, `--mode=interpreter --no-cache`):

| probe | 2026-09-06 verdict | today |
|---|---|---|
| `test/01_unit/compiler/lint/linear_scan_in_loop_spec.spl` | (rule never ran) | **8/8 PASS** |
| `bin/simple lint src/app/devhub/retry.spl` (original repro) | `error: class CodeLine has no field named code`, exit 0 lie | **"Lint passed: all files clean"** |

The `PERF-SCAN-001` rule now executes; the whole-linter abort and the
exit-0-despite-analyzing-nothing shape are gone. (The sibling "linter must exit
non-zero on abort" item was separately fixed by the fail-closed work recorded
in `mcdc_wrapped_copy_undefined_identifier_dir_only_2026-09-02.md`'s runner and
the 2026-09-12 degrade; not re-litigated here.)
