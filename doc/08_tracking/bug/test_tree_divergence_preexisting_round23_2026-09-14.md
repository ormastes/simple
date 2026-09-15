# Pre-existing test-tree divergence recorded for the round-23 parity landing (2026-09-14)

`check-test-tree-divergence.shs` is RED on `origin/main` and has been for
several days. The round-23 web↔Chrome parity change
(`doc/10_metrics/ui/web_chrome_parity_round23_2026-09-14.md`) lands on the
scoped-delta escape in `.claude/rules/vcs.md`, which REQUIRES the pre-existing
offender list to be recorded before landing. This file is that record.

## Range

    BASE e080ed65435a07bafe356f3a687f1aebd8c20da6   (origin/main at landing)
    NEW  882aff389c814bf0faa88dd8897d572b1b7e22ae   (the round-23 commit)

## Verdicts, verbatim

    check-test-tree-divergence-delta: base verdict: check-test-tree-divergence:
      FAIL — 3945 diverged vs 965 baselined (3083 new, 103 fixed-but-still-baselined);
      32 mirror-only (31 unallowlisted, 0 stale-allowlist);
      half-landed: skipped (no --base)
    check-test-tree-divergence-delta: PASS — 3217 pre-existing offender(s),
      0 introduced by this range

Exit code 0, captured into a variable on the line after the invocation, not
through a pipe.

## Offender list identity

3,945 lines. SHA-1 of the saved list: `f1f453e8cbece5dc848c3fa4b3c4e079eae1d5ef`.
First three entries:

    integration:app/add_remove_log_modes_spec.spl
    integration:app/app_mcp_intensive_spec.spl
    integration:app/brief_log_modes_spec.spl

## Mirror pairs this range touches

Enumerated rather than asserted:

    git diff --name-only BASE..NEW -- test/01_unit test/unit test/02_integration test/integration
    test/01_unit/browser_engine/pre_newlines_and_overflow_wrap_normal_spec.spl

One new file, with no twin on either side, and the delta guard's own
offender-list diff — which is the authority, not this enumeration — reports 0
introduced.

## Not a fix

This record admits one landing over a pre-existing red. It does not reduce the
divergence, and `--generate-baseline` was NOT run: 3,083 of the offenders are
new relative to the baseline, i.e. real accumulated debt, and regenerating the
baseline would hide it.
