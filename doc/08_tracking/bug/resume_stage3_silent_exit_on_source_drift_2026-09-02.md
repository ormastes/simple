# `resume-stage3-from-admitted.sh` exits SILENTLY (rc=1, zero output) when sources drift

**Status:** OPEN
**Filed:** 2026-09-02
**Severity:** P2 — the refusal itself is CORRECT; the silence is the defect. Costs an
operator an open-ended debugging session for what should be a one-line message.

## Symptom

```
$ sh scripts/bootstrap/resume-stage3-from-admitted.sh build/bootstrap
$ echo $?
1
```

**Zero bytes on stdout and stderr.** No error, no hint, no indication which of the
several preflight conditions failed. The bootstrap wrapper that calls it reports only
`stage3_rc=1` / `NO stage3 log`, which reads as "Stage 3 failed" rather than "Stage 3
was never started, on purpose".

This is the same UNDIAGNOSABLE class as
`simpleos_stage2_bootstrap_sanity_exit2_without_diagnostic_2026-08-20.md`, which the
same file's own header comment cites as the reason its `bootstrap_stage3_error()` helper
always states a reason. That discipline was not applied to these three lines.

## Root cause

`scripts/bootstrap/resume-stage3-from-admitted.sh:262-264`, under `set -eu`:

```sh
cmp -s "$source_before"  "$resume_source_check"
cmp -s "$git_before"     "$resume_git_check"
cmp -s "$tool_before"    "$resume_tool_check"
```

`cmp -s` is silent by contract. Under `set -e` a non-zero status aborts the script
immediately, so a legitimate "the tree changed since the interrupted run" verdict is
delivered as an unexplained exit 1. The identical shape recurs at `:543-544` for the
post-build comparison.

## How it was hit

The Stage-3 build tree was deliberately synced forward (`git checkout -f --detach
origin/main`, 42 commits) to pick up fixes that had landed. `source-inputs-before.txt`
still described the PREVIOUS tree, so the source snapshot legitimately differed and the
resume refused — correctly, since resuming would compile different sources than the
recorded baseline. Diagnosing that required `sh -x` and reading the trace to find which
statement aborted.

## The refusal is right; only the reporting is wrong

Do NOT "fix" this by deleting the baseline files or relaxing the comparison. A resume
that silently compiles a different source set than it recorded is exactly the failure
this guard exists to prevent. The correct action for an operator is a FRESH Stage 3, not
a resume.

## Suggested fix

Give each comparison a verdict, matching the file's own existing convention:

```sh
cmp -s "$source_before" "$resume_source_check" ||
  bootstrap_stage3_error "source inputs changed since the interrupted run \
(baseline $source_before vs current tree); a resume would compile a different source \
set -- run a fresh Stage 3 instead"
```

and likewise for the git-state and tool-authority comparisons, so the operator learns
WHICH of the three drifted. The helper already exists in this file and already prints
`ERROR — nothing was checked (<reason>)`.

## Scope note (honest)

Verified by `sh -x` trace showing the abort at the `cmp -s "$source_before"` line, plus
a direct run producing a 0-byte log with rc=1 (exit status read into a variable on the
line after the invocation, not through a pipe). The `:543-544` post-build pair is the
same shape by inspection; it was not separately triggered.
