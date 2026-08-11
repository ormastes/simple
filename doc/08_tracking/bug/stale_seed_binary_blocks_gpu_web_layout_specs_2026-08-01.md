# Stale deployed `bin/simple_seed` blocks every spec importing `browser_renderer_protocol.spl`

**Date:** 2026-08-01
**Status:** ALREADY-FIXED (re-verified 2026-08-09) — the grammar fix
(`023a60a05aa`) is in source, and the deployed binary has since been
redeployed. Re-verified fresh: `bin/release/x86_64-unknown-linux-gnu/simple`
is now dated Aug 9 04:50 (was Jul 25 04:18 at filing), and
`bin/simple run src/lib/common/web/browser_renderer_protocol.spl` no longer
reproduces the `Unexpected token: expected expression, found Newline` parse
error at lines 575/583 — it proceeds past parsing into normal lint/use-warning
output. The regression-coverage context added at filing time
("implicit trailing-operator continuation (no backslash)",
`test/03_system/feature/usage/line_continuation_spec.spl`) already guards
against this recurring. Original text below is left intact for history.
**Severity:** HIGH — both `test/01_unit/lib/gpu_web/layout/*_spec.spl` specs and
every other spec that transitively imports
`src/lib/common/web/browser_renderer_protocol.spl` fail to COMPILE, so they have
never run.
**Found by:** parse-blocker lane, reproducing a sibling lane's report.

## Symptom

```
error: compile failed: parse: in
  "src/lib/common/web/browser_renderer_protocol.spl":
  Unexpected token: expected expression, found Newline
```

No line or column is reported. Reproduced at pristine tip `3c4caeaf984`
(archived to tmpfs; the shared working copy was not touched):

| Spec | `bin/simple_seed` (Jul 25 build) | `simple.pre-segv-fix-20260731` (Jul 30 build) |
|---|---|---|
| `test/01_unit/lib/gpu_web/layout/web_layout_manager_spec.spl` | parse error, exit 1 | 4 examples, 0 failures |
| `test/01_unit/lib/gpu_web/layout/web_layout_incremental_oracle_spec.spl` | parse error, exit 1 | 9 examples, **1 failure** |

## Root cause — an ALREADY-FIXED grammar gap in a NOT-yet-redeployed binary

The offending construct is a trailing comparison operator continuing onto the
next physical line, at `browser_renderer_protocol.spl:575` and `:583`:

```simple
    if payload_bytes.len().to_i64() >
       BROWSER_RENDERER_MAX_PAYLOAD_BYTES - capability_bytes:
        return _browser_renderer_reject_encode("payload-too-large")
```

Minimised to a 7-line file, this reproduces the identical error on the stale
seed and runs correctly on the newer binary. So the file is fine and the
grammar is fine; the deployed parser is old.

This is exactly the defect recorded in
`doc/08_tracking/bug/if_condition_operator_line_continuation_parse_2026-07-30.md`,
fixed on 2026-07-30 in `023a60a05aa`. Both current parsers carry the fix:

- Rust seed: `src/compiler_rust/parser/src/expressions/binary.rs`,
  `parse_equality` (line ~199) and `parse_comparison` (line ~244) both call
  `skip_newlines_and_indents_for_method_chain()` after consuming the operator.
- Pure-Simple frontend: `src/compiler/10.frontend/core/tokens.spl`
  `token_requires_rhs()` returns true for `TOK_LT`/`TOK_GT`/`TOK_LT_EQ`/
  `TOK_GT_EQ`/`TOK_EQ`/`TOK_NOT_EQ`, and
  `src/compiler/10.frontend/core/lexer_struct.spl:1238` suppresses the newline
  on that basis (G27).

`bin/release/x86_64-unknown-linux-gnu/simple_seed` is dated **Jul 25 04:18** —
five days older than the fix. It is a gitignored build artifact, so no commit
can repair it.

## Why this stayed invisible

`test/03_system/feature/usage/line_continuation_spec.spl` covered only the
EXPLICIT backslash (`\`) continuation form. The implicit trailing-operator form
— the one that regressed and the one the library file uses — had no coverage at
all. Closed in this change: a new context
"implicit trailing-operator continuation (no backslash)" with four examples
(`val` with `>`, `val` with `==`, `if` condition, `while` condition). Verified
RED on the stale seed (whole-file parse error) and GREEN on the fixed parser.

## Remediation

1. Rebuild and redeploy `bin/release/x86_64-unknown-linux-gnu/simple_seed` from
   a tree at or after `023a60a05aa`. Until then, any lane invoking
   `bin/simple_seed` — including `simple test`, which delegates to the seed
   child — cannot compile these modules.
2. The live `bin/simple` (130 MB, Jul 31) is separately unusable: it rejects a
   bare `.spl` positional with `error: unknown command`, so it is not a
   fallback. Tracked separately.
3. Add the deployed-binary vintage to the redeploy checklist: a parser fix that
   is not redeployed is indistinguishable from a parser fix that never landed.

## Do NOT

Do not rewrite `browser_renderer_protocol.spl:575`/`:583` to dodge the parse
error. The source is correct under the current grammar; normalising it to a
workaround would hide the stale-binary problem and re-open the coverage gap.
