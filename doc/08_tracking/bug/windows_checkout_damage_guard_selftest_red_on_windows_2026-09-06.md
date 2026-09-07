# check-windows-checkout-damage selftest red on Windows: MSYS `grep` strips CR, so the CRLF signature never fires

- **Filed:** 2026-09-06
- **Severity:** high — `push-windows-checkout-damage` is a PUSH-BLOCKING gate
  (`config/check/must_check_gates.sdn`). Its selftest is fatal, so on Windows the guard
  refused to run at all and could never produce a verdict on the one platform it was
  written to protect; every push from this box needed `--no-verify`.
- **Status:** FIXED (2026-09-06)
- **Platforms:** Windows 11 / Git Bash (MSYS2). Linux/macOS unaffected (GNU grep there is
  byte-oriented and matches `\r$` correctly).

## Summary

Signature 3 of the guard ("newly-introduced CRLF in a tracked text blob") was implemented as
`LC_ALL=C grep -q "$(printf '\r')$" "$SCRATCH/blob"`. MSYS/Git-Bash `grep` opens its input in
TEXT mode and strips a trailing CR from each line *before* matching, so the pattern `\r$` can
never match on Windows. `blob_has_crlf` therefore always returned "no CRLF", fixture 3
(`new-crlf-owned`) expected verdict 1 and got 0, the fatal selftest tripped, and the guard
exited 2 (`ERROR — nothing was checked`).

This is the same class of defect as
`doc/08_tracking/bug/guard_wiring_selftest_red_on_windows_2026-09-06.md` (a POSIX-shell guard
depending on a tool whose Windows build has different byte/path semantics), but a different
mechanism: there the offender was a NATIVE `rg` mangling paths; here it is MSYS `grep`'s text
mode eating the very byte being searched for. Note the symlink signatures (1 and 2) were fine —
only the CRLF signature was blind, which is precisely the damage class Windows produces most.

## Evidence (before)

```
$ sh scripts/check/check-windows-checkout-damage-push.shs --selftest
check-windows-checkout-damage-push: SELFTEST FAIL — new-crlf-owned: expected verdict 1, got 0 (offenders: )
check-windows-checkout-damage-push: selftest FAILED (1/7 fixtures wrong)
```

Isolated proof that the blob is correct and `grep` is the liar:

```
$ printf 'alpha\r\nbeta\r\n' > f.txt
$ od -c f.txt | head -2
0000000   a   l   p   h   a  \r  \n   b   e   t   a  \r  \n
0000015
$ LC_ALL=C grep -q "$(printf '\r')$" f.txt; echo "grep_rc=$?"
grep_rc=1            # <-- file demonstrably has CRLF; grep says no
$ which grep
/usr/bin/grep        # MSYS grep
```

`git hash-object -w --stdin` and `git cat-file blob` were verified byte-exact, so the fixture
harness and the temp-index tree construction were never at fault.

## Fix

`scripts/check/check-windows-checkout-damage-push.shs`, `blob_has_crlf()` only. Detect the CR-LF
pair byte-wise with `tr`, which is binary-clean on both platforms:

```sh
LC_ALL=C tr -c '\r\n' 'x' < "$SCRATCH/blob" \
    | LC_ALL=C tr -s 'x\r' 'xR' \
    | LC_ALL=C grep -q 'R$'
```

Every byte that is not CR or LF becomes `x` (this also removes NULs, so `grep` cannot declare the
stream binary and bail); runs are squeezed; CR becomes a printable `R`. A CRLF reduces to `R\n`,
while a lone CR keeps a following `x`, so `R$` is true iff a CR is immediately followed by LF —
exactly the original intent, and no CR ever reaches `grep`. Pure POSIX `sh` + `tr` + `grep`; no
Windows branch, no bypass, no weakened or deleted fixture, selftest still fatal.

## Evidence (after)

```
$ sh scripts/check/check-windows-checkout-damage-push.shs --selftest
check-windows-checkout-damage-push: selftest 7/7 fixtures correct

$ sh scripts/check/check-windows-checkout-damage-push.shs --scan-only 'origin/main..c9821b50cbb39d8b3bbc3f1e3fd1a8de8b9878f9'
check-windows-checkout-damage-push: selftest 7/7 fixtures correct
PASS — 31 path(s) checked in origin/main..c9821b50cbb39d8b3bbc3f1e3fd1a8de8b9878f9, 0 Windows-checkout damage (0 materialized symlinks, 0 absolute Windows symlink targets, 0 newly-CRLF files)
```

The range was independently confirmed damage-free (0 symlinks materialized, no CRLF introduced,
5 genuinely-new files), so PASS is a true verdict and not a re-run of the old blindness — fixture
3 now proves the detector fires on real CRLF.

## Not verified

- Not re-run on Linux in this session. The change replaces one POSIX pipeline with another and
  `tr -c`/`tr -s` are POSIX-specified, but a Linux CI run of `--selftest` is still the confirming
  step.
- Unchanged and still true of the guard: it reads COMMITTED content only, and `--scan-only` is a
  no-op alias since the guard never mutates.
