# Push gates were unrunnable on macOS: two BSD-awk incompatibilities

**Status:** RESOLVED (both awk defects) — re-verified on macOS aarch64 (BSD awk)
at `origin/main@b9667d6584f`, 2026-09-12. See "Verification 2026-09-12" at the
end of this record. The record's item 3 (stale `no-direct-rt` baseline at the
widened roots) is NOT this bug and is NOT resolved here — it is scope/mode
debt owned by the roots-widening lane; the push tier runs `--roots src`, so it
is not what enforces.

**Date:** 2026-09-03 (both awk defects were fixed upstream, NOT by this record's
own change — see the 2026-09-04 amendment; a third, pre-existing blocker is
documented below and is out of scope)

> **Amended 2026-09-04.** This record originally shipped alongside its own two
> code fixes. On rebase both were dropped as already upstream: `origin/main`
> had landed equivalent fixes independently — `-v required="$(printf '%s' ...
> | tr '\n' ' ')"` with `split(required, required_ids, /[ \n]+/)` in
> `check-push-must-pass.shs`, and `tr -dc '\0' | wc -c` in
> `check-no-direct-rt.shs`. Both were verified present before the drop. The
> diagnosis below stands and is why this record is kept; only the claim that
> the fixes ride in this change was wrong.

`check-push-must-pass.shs` is, per `.claude/rules/vcs.md`, "the single
authoritative enforcement surface" for the push tier. On macOS it could not pass
at all. Two independent GNU-awk-isms, both of which fail *closed* and both of
which reported a misleading cause.

## 1. `awk -v` cannot carry a newline (BSD/POSIX)

`REQUIRED_BOOTSTRAP_IDS` is a newline-separated id list passed as
`-v required="$REQUIRED_BOOTSTRAP_IDS"`. POSIX/BSD awk rejects a newline inside a
`-v` assignment outright:

```
awk: newline in string compiler-stage1 comp... at source line 1
```

awk then exits non-zero, `validate_ledger_text` returns failure, and the caller
dies with:

```
push-must-check: FAIL — ledger is malformed stale or has a non-passing push-blocking row
```

That message sent the investigation at the ledger and the manifest. **Both files
are well-formed** — checked for unbalanced quotes and embedded newlines at
`origin/main`, zero rows flagged. The ledger was never the problem.

**Fix:** pass the value through `ENVIRON` instead, which carries newlines intact
on both awks, leaving `split(required, required_ids, "\n")` unchanged.

Control (this host): `awk -v v="$(printf 'a\nb\n')" '{print}'` reproduces the
error; via `ENVIRON` it does not.

## 2. `RS = "\0"` is a GNU extension; BSD awk reads it as paragraph mode

`check-no-direct-rt.shs` counted a NUL-delimited `find -print0` manifest with
`awk 'BEGIN { RS = "\0" } END { print NR + 0 }'`. BSD awk truncates the `"\0"`
literal to `""`, which selects **paragraph mode**, so any NUL-delimited manifest
collapses to a single record and the count is always 1.

Symptom — selftest fixture 4 failing with:

```
ERROR — selftest failed: hidden/ignored files not scanned equivalently (got '1 2 0 2 0')
```

which reads like a traversal bug. It is not: reproducing the fixture by hand,
**`find` and `rg` each returned 2 files, in agreement**. Only the count was
wrong, and only the first field (`$1=1`, while `$2` and `$4` were the expected
`2`).

Control (this host): `printf 'a\0b\0c\0' | awk 'BEGIN{RS="\0"} END{print NR}'`
prints **1**; `tr -cd '\0' | wc -c` prints the correct **3**.

**Fix:** count NUL terminators with `tr -cd '\0' | wc -c`.

Two other `RS="\0"` sites were found and deliberately left alone:
`check-no-direct-rt.shs:106` (`rt_normalize_seps`, a Windows path-separator
rewrite that is a no-op on this platform) and
`check-heavy-work-preflight.shs:161` (reads `/proc/<pid>/cmdline`, Linux-only).

## 3. Still blocking, pre-existing and NOT fixed here: a stale `no-direct-rt` baseline

With both fixes in, the gate runs and reports a real ratchet failure:

```
FAIL — forbidden direct rt_* count 27608 exceeds baseline 7776
  (roots=src,examples,tools,scripts,test, src=6447 examples=1344 tools=14 scripts=308 test=19495)
```

Scoped to the pre-widening roots it is green:

```
PASS — 16238 file(s) scanned (roots=src, src=6447), forbidden=6447, ... (baseline 7776)
```

So the baseline in `scripts/check/no_direct_rt_baseline.txt` was never
regenerated for the 2026-08-28 `--roots` widening; `test/` alone contributes
19,495 of the 27,608. `src` is comfortably *under* baseline and even improved
(6447 < 7776).

**Deliberately not "fixed" with `--generate-baseline`.** That flag is for
reviewed updates only, and regenerating here would ratchet ~20k call sites of
unreviewed debt into the accepted baseline. Whoever owns the widening should
decide: re-baseline at the wider scope, or narrow the gate's default roots back
to `src`.

## Note: `land.shs` reports success on a failed push

`sh scripts/check/land.shs --submit` returned **rc=0** and printed
`land.shs: submitted work/...` while the underlying `git push` had failed with
`error: failed to push some refs`. It does not propagate the push's exit status,
so a blocked push reads as a successful landing.

## Triage 2026-09-12

Status line inserted mechanically by the bug-db triage (record had no parseable `Status:` line); rule: filed before 2026-07-29 with no cheap repro → CLOSED-STALE, otherwise OPEN (unverified).

## Verification 2026-09-12 (macOS aarch64, Darwin 25.5.0, BSD awk)

Both awk fixes are present at `origin/main@b9667d6584f` and were landed upstream,
not by this record's own change (as the 2026-09-04 amendment already said):

1. **`awk -v` newline** — `scripts/check/check-push-must-pass.shs:154` now reads
   `-v required="$(printf '%s' "$REQUIRED_BOOTSTRAP_IDS" | tr '\n' ' ')"`. The
   newline never reaches `-v`, so BSD awk's `newline in string` rejection cannot
   fire. Landed `e09f6b9ac66`.
2. **`RS="\0"` paragraph mode** — `scripts/check/check-no-direct-rt.shs` counts
   NUL terminators with `tr`, and carries an explicit comment at :281 recording
   that BSD awk does not honour `RS="\0"`. Landed `e09f6b9ac66`.

Oracle for item 2 run on this host — the guard's own fixture 4 is the RS="\0"
replay, and it passes:

```
$ sh scripts/check/check-no-direct-rt.shs --selftest-only ; echo rc=$?
PASS — 20 selftest fixture(s) checked
rc=0
```

(19 fixtures before this change; fixture 20 is the new missing-option-value
fixture added in the same PR, see below.)

## Defect found and FIXED during this verification: a blocking push gate died with no verdict

Running the exact push-tier form of the blocking `push-no-direct-rt` row with
its option value omitted:

```
$ sh scripts/check/check-no-direct-rt.shs --roots src --rev
scripts/check/check-no-direct-rt.shs: line 105: $1: unbound variable
```

Exit 1, **no verdict line on stdout at all**. Five value-taking options
(`--offenders`, `--root`, `--roots`, `--rev`, `--baseline-rev`) were parsed as
`shift; VAR="$1"`, so an option in last position shifted the list empty and then
expanded `"$1"` under `set -u`. `.claude/rules/vcs.md` requires the verdict to be
the last stdout line, PASS/FAIL/ERROR — a raw shell trace is none of those, and a
caller reading the last stdout line to classify the gate sees nothing. The
failure was fail-CLOSED (non-zero), so it never laundered a pass; it was
unreadable, not unsafe.

Fixed by routing every value-taking option through a `require_value()` helper:

```
$ sh scripts/check/check-no-direct-rt.shs --roots src --rev
ERROR — nothing was checked: --rev requires a value        (exit 2)
```

Sabotage triple:
- **fix in, valid input** — `--roots src --rev HEAD` output is byte-identical to
  the pre-fix run (`diff` of the two captured logs is empty); the fix changes no
  verdict.
- **fix in, sabotaged input** — all five options bare produce the ERROR verdict
  on stdout with exit 2.
- **fix reverted** — the new selftest fixture 20 catches it:
  `ERROR — selftest failed: --rev with no value did not emit the ERROR verdict on stdout (rc=1, out=[])`.

Fixture 20 asserts both channels (verdict text on stdout AND exit status 2) for
every one of the five options, so removing the guard on any single option fails
the selftest.

### Two-spec rule

- **Reproducing fixture:** selftest fixture 20, which replays the exact failing
  shape (`--rev` with no value) and asserts the ERROR verdict on stdout plus
  exit 2.
- **Generalization probe:** the same fixture covers all FIVE value-taking
  options, not just the one that was reproduced, so the adjacent code paths are
  pinned rather than only the reported one. Widened beyond this file, the other
  six blocking push-tier guards were scanned for the same `shift; VAR="$1"`
  shape and all report **0** sites:
  `check-c-runtime-compiles-push`, `check-guard-wiring`,
  `check-main-test-runnable-push`, `check-rt-dual-implementation-ratchet`,
  `check-runtime-source-list-parity`, `check-port-io-single-owner`.
  `check-no-direct-rt.shs` was the only guard carrying the defect, so there is
  no second file to fix and no second fixture to add.

### Test-tree divergence step-over, recorded per `.claude/rules/vcs.md`

`check-test-tree-divergence` is RED at both refs on this range — pre-existing,
owned elsewhere. This branch touches zero files under `test/`, so the scoped
delta is clean:

```
$ sh scripts/check/check-test-tree-divergence-delta.shs origin/main HEAD
check-test-tree-divergence-delta: pre-existing red is identical at BASE and NEW;
  this range introduces nothing
check-test-tree-divergence-delta: base verdict: check-test-tree-divergence:
  FAIL — 3943 diverged vs 965 baselined (3081 new, 103 fixed-but-still-baselined);
  26 mirror-only (25 unallowlisted, 0 stale-allowlist)
check-test-tree-divergence-delta: PASS — 3209 pre-existing offender(s),
  0 introduced by this range
```

The pre-existing diverged-offender list is 3,943 entries; it is recorded here by
reference (the helper's saved `test_tree_divergence_preexisting.txt`) rather than
inlined, and the counts above — 3943 diverged / 965 baselined / 3081 new / 103
fixed-but-still-baselined / 26 mirror-only / 3209 offenders — are the identifying
fingerprint of that list at this base. Landing on a delta-PASS requires this
record to exist; it is not a licence to ignore the underlying red.

### Not clean on this range: `check-guard-wiring` (pre-existing, zero delta)

```
FAIL — 1682 guard(s) checked, 1 NEW unwired (607 baselined as known debt)
unwired_guard=check-test-runner-executes-bodies.shs
```

Byte-identical when run against `--rev origin/main`, so this branch contributes
nothing to it. The file was ADDED by `dec6eb336e9` ("fix(test-runner):
calibration gate for a load-only `simple test`, and honour --no-limits in safe
mode"), which is lane 3's territory, not lane 2's — this branch does not touch
it. It was `PASS — 1679 guard(s) checked … 0 NEW unwired` at `b9667d6584f`, the
base this branch was first written on, which dates the regression to a merge
into `main` between those two tips. Per vcs.md the scoped-delta escape exists
for the divergence guard ONLY, so this is reported rather than stepped over.
