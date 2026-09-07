# check-guard-wiring selftest red on Windows: native `rg` path mangling breaks the reachability scan

- **Filed:** 2026-09-06
- **Severity:** high — `push-guard-wiring` is a PUSH-BLOCKING gate (`config/check/must_check_gates.sdn`);
  on Windows it could not produce a verdict, so every push from this platform needed `--no-verify`.
- **Status:** FIXED (2026-09-06)
- **Platforms:** Windows 11 / Git Bash (MSYS2) with a NATIVE `rg` on PATH. Linux/macOS unaffected
  (their `rg` is the same POSIX-path universe as `find`).

## Summary

`scan_wiring` builds the reachability graph by using `rg -l` to list files that mention a guard
basename, and it uses those file paths as BFS edge keys against a root set produced by `find`.
`rg` here is the only NATIVE (non-MSYS) tool in the pipeline: given an absolute POSIX argument
such as `/tmp/tmp.XXXX/scripts`, MSYS argv translation rewrites it to `C:/Users/.../Temp/tmp.XXXX/scripts`
and `rg` emits Windows separators (`...\w.yml`). Those strings never string-equal the
`find`-produced `/tmp/tmp.XXXX/.github/workflows/w.yml` roots, so `awk -F'\t' '$1==F'` matched
nothing, the BFS reached **zero** guards, and every guard was reported orphaned.

Verified pre-existing: reproduced from a pristine `origin/main` `git archive` of `scripts/check` +
`config/check`, with no local edits present.

## Evidence (before)

```
$ sh scripts/check/check-guard-wiring.shs --selftest
SELFTEST FAILED: guard named only inside a lib helper is still reachable (expected 'yes', got 'no')
SELFTEST FAILED: guard named only inside a lib helper is not an orphan (expected 'no', got 'yes')
SELFTEST FAILED: direct guard reachable (expected 'yes', got 'no')
SELFTEST FAILED: indirect guard reachable (expected 'yes', got 'no')
SELFTEST FAILED: reachable guard is NOT an orphan (expected 'no', got 'yes')
SELFTEST FAILED: unjustified set is exactly st-orphan.shs (expected 'st-orphan.shs',
                 got 'st-direct.shs st-indirect.shs st-orphan.shs st-viahelper.shs')
SELFTEST FAILED: baselined guard that became wired is stale (expected 'st-direct.shs', got '')
check-guard-wiring: SELFTEST FAILED -- the wiring scan is broken.
```

Isolated proof of the mangling:

```
$ T=$(mktemp -d); rg -F -f "$T/pat" -l --no-ignore --hidden "$T/a"
C:/Users/ormas/AppData/Local/Temp/tmp.v62BMw0kuv/a\w.yml
$ find "$T/a" -type f -print
/tmp/tmp.v62BMw0kuv/a/w.yml
```

## Fix

`scripts/check/check-guard-wiring.shs`, the `rg` branch of step 3 only. Run `rg` from **inside**
`$_root` on RELATIVE search dirs (no absolute POSIX argument to mangle), then normalise `\` to `/`
and re-prefix `$_root/`. On Linux the search dirs are the same directories and the output is
byte-identical to the previous absolute-path invocation, so the Linux path is unchanged.
Pure POSIX `sh` (subshell `cd`, `sed`, `tr`); no bashism, no MSYS-only tool, no Windows-only
branch, no fixture weakened or deleted.

## Evidence (after)

```
$ sh scripts/check/check-guard-wiring.shs --selftest
check-guard-wiring: selftest 20/20 fixtures correct        (rc=0)

$ sh scripts/check/check-guard-wiring.shs
check-guard-wiring: PASS — 1559 guard(s) checked, 402 invoked, 1138 orphaned
(735 baselined as known unwired debt, rest justified), 0 NEW unwired, 0 copied hook(s)
```

Non-vacuous: 1559 guards enumerated and 402 reached, versus 0 reached before the fix.

## Not verified here

- The Linux transcript was not re-run on a Linux host from this session; equivalence is argued
  from the fact that `cd $_root` + relative dirs + `tr`/`sed` normalisation is a no-op there.
  Compensating empirical evidence: the real scan reconciled cleanly against the 735-entry
  unwired baseline, which was generated on Linux. The ratchet fails on stale baseline (a
  baselined guard that became reached, or one that vanished), and the run reported `0 NEW
  unwired` with no staleness — so the Windows scan reproduced the Linux-generated reachability
  partition, not merely "some" partition.
- The second `rg` call site, `_fixed_strings_only` (`rg -o -F -f "$1"` reading stdin), was
  checked and needs no change: MSYS translates its absolute pattern-file argument into a VALID
  Windows path, so the file still opens, and the selftest's reached/edges assertions exercise
  it end to end.
- `installed_hooks=0` on this box (no repository-local hook installation to evaluate); the
  hook-shape fixtures in the selftest do cover that code path.
