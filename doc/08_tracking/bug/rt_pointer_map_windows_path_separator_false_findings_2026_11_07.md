# Windows pointer-map baseline keys use the wrong path separator

- Severity: P2
- Status: open pending PR landing; checker repair verified below.
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
until this repair lands through its reviewed release-branch PR.
