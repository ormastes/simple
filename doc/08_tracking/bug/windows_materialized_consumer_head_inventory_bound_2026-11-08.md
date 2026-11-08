# Windows materialized consumer rejects the full tracked HEAD inventory

Status: fix implemented; focused native regression passes; canonical bootstrap
verification remains pending. This is not Stage2 admission or seed qualification.

At frozen source `5fffbebf99d651e86fc3e57e2089537250916004`, canonical MSVC
seed-refresh attempt4 stopped before Cargo with `stage3-materialized-consumer:
command.io`. The standalone materializer had passed: 65 records, 61 conversions,
four exact allowlisted pending tool/skill links and zero failed records.

The consumer's exact `git ls-tree -rz -r --full-tree HEAD` output measured
16,851,602 bytes. Its ordinary command reader admitted at most 16,777,216 bytes,
so this valid inventory exceeded the limit by 74,386 bytes. The asynchronous
reader raised `bound.command-output`; the command coordinator hid that cause
behind `command.io`. Neither missing links nor unavailable MSVC caused this exit.

The repair gives only tracked-tree enumeration a separate 64MiB output limit.
Ordinary command stdout and all stderr remain bounded at 16MiB. Existing entry,
time and aggregate input budgets remain enforced. Asynchronous I/O failures now
name the stream and preserve the actual cause. No input validation is bypassed.

`scripts/check/check-materialized-consumer-output-bounds-windows.ps1` extracts
the complete production C# consumer and executes real subprocess fixtures:

- A valid 130,000-row inventory above 16MiB parses through `HeadLinks`.
- An ordinary 17MiB output fails the existing 16MiB bound.
- A tree output of 64MiB plus one byte fails the separate finite tree bound.
- A real command exit42 remains a command failure.

All four focused cases passed on Windows. Retained evidence is outside mutable
worktrees at `D:/dev/msvc-bootstrap-evidence-20261108/`, including
`canonical-msvc-seed-full-checkout-20261108/canonical.env`, its command log,
`full-checkout-links.env` and `consumer-inventory-overflow.sdn`. The focused
regression log is `D:/dev/materialized-consumer-bounds-20261108-validation.txt`.

Removal check: a newly frozen source including the reviewed repair must pass
the canonical native materialized consumer and reach the actual MSVC seed
compiler invocation. A passing focused fixture alone does not close this bug.
