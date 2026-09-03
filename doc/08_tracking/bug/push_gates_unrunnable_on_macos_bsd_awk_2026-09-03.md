# Push gates were unrunnable on macOS: two BSD-awk incompatibilities

**Date:** 2026-09-03  **Status:** both fixed in this change; a third, pre-existing blocker documented below

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
