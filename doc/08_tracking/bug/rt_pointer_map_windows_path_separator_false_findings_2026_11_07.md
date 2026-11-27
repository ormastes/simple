# Windows pointer-map baseline keys use the wrong path separator

- Severity: P2
- Status: FIXED — scoped mapping-checker repair merged in PR #7336; retained verification below is unchanged.
- Owner: `scripts/check/check-rt-pointer-ref-map.py`, lines 241 and 251.
- Session: `01a1afac/pointer-map-windows`.

## Failure and cause

The existing Windows run reported ten new SRT003 parameter-count findings and
ten stale baseline entries. The retained paired proof establishes that replacing
the Windows separators in every new key gives exactly the ten stale keys and
the complete tracked baseline. The ABI discrepancies themselves are existing
baseline entries, not new source regressions.

`scan()` computed `rel` with `os.path.relpath`, which returns backslashes on
Windows, while tracked baseline keys use forward slashes. It also recomputed
the unnormalized relative path for return keys. The checker blob
`2d7616d976d99e36127a31a63b461ca7ed8af84f` is identical at the retained failing
baseline `7cec6a54ea8` and this lane's initial release base
`3c63201ea63a1f2995f614452e02155781a6aaa8`.

## Repair

Normalize the existing `rel` once with `.replace(os.sep, '/')`, then reuse it
for both parameter and return keys. The arity logic, classifiers, baseline
contents, source inventory, and enforcement policies are unchanged. On POSIX,
the replacement preserves the existing separator spelling.

## Executed verification

Both checks ran once after the two-line repair on native Windows Python 3.13:

1. `python scripts/check/check-rt-pointer-ref-map.py --selftest`: exit 0;
   **PASS: 15 return, 8 enforced, 27 parameter cases**. Expected failing negative
   fixtures remain in the full log; its final self-test verdict is PASS.
2. `python scripts/check/check-rt-pointer-ref-map.py --root C:/dev/wt/nativeall-scalars-d88f`:
   exit 0; **PASS: 265 return edges, zero new findings**. Coverage is 142 return
   symbols, 11 enforced returns, 63 raw returns, 131 UNKNOWN returns; 3,856
   parameter edges, 1,433 pointer parameters, two unparsed parameters, and ten
   existing SRT003 entries. These counts are mapping evidence only; compilation
   and linking remain UNTESTED by this checker.

The existing complete scalar worktree was read only; it was not modified or
materialized into this small checker worktree. No baseline regeneration, new
test helper, source mirror, compiler build, or Rust-seed fallback was used.
Root reviewed and accepted the exact two-line source diff and executed evidence
before metadata, commit, or publication work.

Retained evidence:
`C:/dev/simple/.git/worktrees/pointer-map-windows-d88f/evidence/` contains
`prior-paired-proof.txt`, `selftest.log`, `selftest.exit`,
`full-nativeall-source.log`, and `full-nativeall-source.exit`. The original
failing proof/log remain under the `nativeall-scalars-d88f` evidence directory.
Provider input/output/cache-read/cache-create token counts, comparable cohort
average, and ratio are unavailable; no zero-filled or estimated usage is claimed.

This scoped checker PASS does not qualify compiler/runtime ABI behavior or
complete the wider MIR/codegen P0–P3 campaign. The root owns the canonical claim
until this repair lands through its reviewed release-branch PR (historical statement, superseded below).

## Release status reconciliation (2026-11-08)

The original repair merged into `release/1.0.0` through
[PR #7336](https://github.com/ormastes/simple/pull/7336) at
`5dba5390b5892dafb363e670aed11acb7741480c` on 2026-11-06T15:36:49Z.
Its reviewed head is `2f7113f062da276e8626169103975ad6f005d390`.
The original exact-head review records P0=0/P1=0, the native Windows
selftest and full mapping scan above, and all ten blocking push gates passing.
The original PR has no conversation comments; structural, RTL source-truth and
component-plan checks succeeded.

Read-only reconciliation pinned release commit
`01a8acae2101320f5c18d52a3e17956f8a2d34f3`, confirmed the original merge is
an ancestor, and compared the complete checker bytes against the merged repair.
They are identical, SHA256
`88a4f449144891a99698ca770c5af1779b9a4e724c6b1f389418f2649fc515d5`.
No already-green checker test was repeated. The raw Windows logs remain at the
original host-local evidence locations above; this reconciliation uses their
tracked report and the original GitHub exact-head review, and does not claim
to have reopened those host-local files on Linux.

The bug's status now reflects the reviewed, tested landing rather than waiting
for a PR that has already merged. Its existing `valid=false` flag is preserved:
that field represents formal record review under the database schema, and no
new raw-log review is claimed here. No compiler, link, runtime, platform ABI or
broader P2 campaign qualification is inferred.
