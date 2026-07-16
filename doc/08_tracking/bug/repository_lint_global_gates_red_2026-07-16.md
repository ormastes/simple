# Repository-wide lint gates are red

Date: 2026-07-16
Status: Open
Priority: P1

## Problem

The repository-wide UI architecture and hot-loop audit scripts currently report
30 and 45 violations respectively. Running those global gates for every focused
`simple lint <path>` invocation made otherwise scoped lint work fail for
unrelated repository debt.

## Current containment

Focused lint checks only the requested scope. `simple lint --all` remains the
explicit owner of both repository-wide gates and still fails when either gate
finds violations.

## Required solution

Classify and repair each reported violation, then retain both scripts as
release-blocking `--all` evidence. Rebaseline only findings individually shown
to be false positives; do not weaken the gates or convert failures to warnings.
