# Windows materializer accepted an ancestor junction cycle

Status: fixed for direct ancestor cycles; Windows regression passed.
Severity: P1 (a successful strict materialization creates recursive checkout topology).

## Reproduction

In a disposable Windows Git repository with `core.symlinks=false`, track
`outer/payload` as an ordinary file and `outer/back` as mode 120000 with the
literal target `../outer`. Run
`sh scripts/setup/materialize-symlinks-windows.shs --strict-missing REPO`.

Before the fix the command exited 0 and reported
`created=1 already_ok=0 skipped_pending(target missing)=0 failed=0 strict_missing=1`.
Reading `outer/back/back/back/payload` returned the original payload. The
materializer had replaced the placeholder with a cyclic NTFS junction.

This violates the existing cycle refusal requirement in
[the materialized alias tracking report](windows_materialized_symlink_alias_git_state_timeout_2026-09-09.md).
It can make directory traversal revisit the same checkout indefinitely. The
reproduction uses strict mode without a receipt, so receipt publication changes
are independent of this defect.

## Change and acceptance criteria

Before creating or accepting a directory junction, compare the target's native
volume and file ID with every held ancestor of the alias path. A match fails with
`target.ancestor-cycle` before placeholder deletion. Identity comparison covers
alternate case and short-path spellings without relying on a textual prefix.

The same validation runs while receipt metadata is captured. This change does
not claim complete graph cycle detection for multiple sibling aliases; the
reported defect and acceptance criteria concern targets that are direct or
indirect filesystem ancestors of their alias.

The regression test is
`test/01_unit/scripts/materialize_symlinks_windows_cycle_test.shs`. It proves:

- A new ancestor junction is refused and its placeholder bytes survive.
- A case-variant target spelling is refused and its placeholder bytes survive.
- An existing ancestor junction is refused during validation.
- A sibling target with a shared textual prefix creates successfully.
- A second materializer pass accepts that valid sibling junction unchanged.

## Verification

Windows/MSYS run on 2026-09-21: **PASS**, exit 0. Output:
`PASS: ancestor cycles refused before mutation; sibling create/idempotence preserved`.

The identical unit test against the unmodified materializer from
`e0dd873da1b7828389db4eb60e82972cc8245313` exited **1** with
`FAIL: accepted ancestor cycle ancestor`. Baseline fixture log:
`D:/materializer-cycle-before/build/test-tmp/materializer-cycle.NSYses/ancestor.log`.

Fixture logs were retained at
`D:/wk-materializer-cycle/build/test-tmp/materializer-cycle.5NOJXA`.
The pre-fix reproduction log is
`D:/materializer-cycle-repro.yaIglW/repro.log`; the cyclic junction was removed
using nonrecursive `Directory.Delete` after collecting evidence.
