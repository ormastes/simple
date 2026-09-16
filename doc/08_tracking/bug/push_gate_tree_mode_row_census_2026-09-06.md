# Census: every `tree`-mode push row, and what each one needs

Companion to
`doc/08_tracking/bug/push_gates_evaluate_working_checkout_not_pushed_commit_2026-09-06.md`,
which records the defect and the incident. This file is the WORK LIST: every
`tree`-mode row in the push tier of `config/check/must_check_gates.sdn`, the
script behind it, and the decision for each.

## The defect, restated in one paragraph

`run_manifest_push_gates` (`scripts/check/check-push-must-pass.shs`) is called as
`run_manifest_push_gates "$_manifest" "$_range" "$_local_sha"`, so its `$_ref` is
**the sha read off pre-push stdin — the commit actually being pushed**. `ref`-mode
rows are handed that sha. `tree`-mode rows are handed nothing and scan whatever
happens to be in the working checkout. With many agent sessions sharing clones,
those two trees routinely disagree, so a `tree`-mode row can report a failure
about content that is not being pushed while staying silent about a regression in
content that is. That is not a weaker gate; it is a gate pointed at the wrong
object.

## Count correction

The earlier note of "16 remaining `tree`-mode rows" is stale — the manifest has
grown. Measured 2026-09-06 at `506601075df` there were **24 `tree`-mode push
rows across 23 distinct ids**, because `push-ui-slim-closure` appeared **twice**,
byte-identically (manifest lines 5 and 30), so the dispatcher ran it twice per
push. That duplicate has been removed.

Reproduce the census:

```sh
grep -n '^    [a-z0-9-]*, push, [a-z]*, tree,' config/check/must_check_gates.sdn
```

### Re-count 2026-09-07 at `60479fbf013`

`origin/main` moves constantly and this file's "24 rows" is now stale. Counting
by TIER and MODE rather than by a bare `, tree,` grep (which spans tiers — it
returns **48**, of which 26 are `ci`-tier and have nothing to do with the push
hook):

```sh
awk -F', ' '/^    [a-z]/ {gsub(/^ +/,"",$1); print $2"\t"$4}' \
  config/check/must_check_gates.sdn | sort | uniq -c
```

| tier | mode | rows |
|---|---|---|
| push | tree | **22** (before this commit's two deletions) |
| push | ref | 7 |
| push | range | 5 |
| ci | tree | 26 |
| bootstrap | automated/receipt/external-receipt/todo | 51 |

Delta from the 24 in the table below: **−1** `push-ui-slim-closure` duplicate
(already removed), **−3** conversions to `ref`
(`type-walk-constructor-parity`, `runtime-source-list-parity`,
`no-mock-file-system-io`), **+1** genuinely new row
`push-port-io-single-owner` (blocking, added 2026-09-06, was NOT in the table
below), **+1** genuinely new row `push-rt-api-groups` — which appeared
**TWICE**, byte-identically in `id:mode:command` (manifest lines 32 and 36; the
two descriptions differ, line 36's is the older and shorter). That is the same
defect as the ui-slim duplicate: the guard ran twice per push. Line 36 and the
duplicate dispatch arm are removed in this commit. `push-rt-dual-implementation`
also converted earlier and no longer counts.

Six of the 22 are **blocking**: `c-runtime-compiles`, `no-direct-rt`,
`port-io-single-owner`, `guard-wiring`, `interpreter-extern-registry-gap`,
`sffi-v2-authority`.

## The dispatcher byte-match check (run this before EVERY push)

Each manifest row's `id:mode:command` must byte-match a case arm in
`run_manifest_push_gates`. An unmatched row hits the fail-closed `*)` arm and
returns 2, which **blocks every push from every session on the machine**. Because
the manifest is read from the pushed sha (`git show "$_local_sha:$MANIFEST_REL"`)
while the dispatcher is the working copy's, a manifest row and its dispatch arm
must ALWAYS move in the SAME commit — otherwise a session that rebases onto the
manifest change without the dispatcher change is hard-blocked.

```sh
awk -F', ' '/^[[:space:]]+[a-z0-9-]+, push,/ {
  id=$1; gsub(/^[ \t]+|[ \t]+$/,"",id);
  mode=$4; gsub(/[ \t]/,"",mode);
  line=$0; sub(/^[^"]*"/,"",line); sub(/".*$/,"",line);
  print id":"mode":"line
}' config/check/must_check_gates.sdn | sort -u > /tmp/mkeys.txt
sed -n "/^run_manifest_push_gates()/,/^}/p" scripts/check/check-push-must-pass.shs \
  | grep -oE "^ *'push-[^']*'\)" | sed "s/^ *'//; s/')$//" | sort -u > /tmp/dkeys.txt
comm -23 /tmp/mkeys.txt /tmp/dkeys.txt   # MUST be empty
```

Measured 2026-09-06: 33 push rows, 37 arms, 0 unmatched. The 4 surplus arms
(`push-no-direct-rt:tree:...` **without** `--roots src`,
`push-outline-parse-terminates`, `push-signature-type-import-provenance`,
`push-use-target-resolves`) match no manifest row and are never executed. The
`push-no-direct-rt` one is actively misleading: an arm sharing an id with a live
row but carrying a different command reads like the manifest row is wrong, when
in fact the live row matches a *second*, correct arm further down.

### Do NOT simply delete those 4 arms (tried 2026-09-06, reverted)

Deleting them was attempted and **turned the BLOCKING `push-guard-wiring` gate
red**, from a clean detached checkout:

```
check-guard-wiring: FAIL — 1595 guard(s) checked, 3 NEW unwired (734 baselined as known debt)
  unwired_guard=check-outline-parse-terminates.shs
  unwired_guard=check-signature-type-import-provenance.shs
  unwired_guard=check-use-target-resolves.shs
```

**`check-guard-wiring.shs` counts a DEAD dispatch arm as wiring.** Those three
guards' only recognised wiring was an unreachable case arm; each also has a
`bootstrap`-tier manifest row, and guard-wiring does not credit that. So the
repo currently has three guards that guard-wiring reports as wired while nothing
can ever execute them from the push path — the same false-assurance shape as the
wrong-tree defect itself, one level up. (`check-no-direct-rt.shs` survived the
deletion because its live `--roots src` arm remains.)

The deletion was reverted rather than "fixed" by editing the guard-wiring
baseline: the red is CORRECT, and silencing it would destroy the finding. The
real repair is either to credit `bootstrap`-tier rows as wiring in
`check-guard-wiring.shs`, or to give those three guards genuine push/CI rows —
both out of scope here, both now visible. Anyone deleting the dead arms must do
that first.

### The hook is bypassed on the PR flow anyway

Worth stating plainly, because it bounds what any of this buys: `main` is
ruleset-protected, so work lands by pushing a `work/*` topic branch and merging a
PR. Topic pushes in this repo are made with `--no-verify` (the hook ends
`BLOCKING gate push-rules-quick failed` on unmodified `origin/main`), and
`--no-verify` skips `check-push-must-pass.shs` **entirely** — dispatcher, every
row, blocking and advisory alike. So these gates being correct is necessary and
not sufficient: the gates now read the right tree *when they run*, and on the
current landing path they do not run. Two follow-ups are implied and neither is
done here: repair `push-rules-quick` so the hook can run unassisted, and mirror
the push tier into the PR's required CI job so bypassing the local hook does not
bypass the gate.

## The fix pattern

`check-rt-dual-implementation-ratchet.shs` (fixed earlier on 2026-09-06) is the
template, and every conversion follows it exactly:

1. `--rev <REV>` materialises the committed tree with
   `git archive <REV> -- <pathspecs> | tar -x` into a temp dir, and scans that.
   `git archive` accepts glob pathspec magic (`':(glob)src/**/*.spl'`), so a
   scanner over one file type does not have to materialise 1.6 GB of `src`.
   A materialised checkout is real files on disk, so this also serves gates that
   must COMPILE or EXECUTE — a separate `git worktree add --detach` is only
   needed when the gate itself runs git commands inside the tree.
2. **The BASELINE / ALLOWLIST is archived from the SAME revision.** Scanning
   committed content against the working copy's baseline is still a wrong-tree
   verdict: a local edit to the baseline, or a checkout predating a baseline
   update, would silently decide the result for content it does not describe.
3. `--generate-baseline` combined with `--rev` and no explicit `--baseline` is an
   ERROR — it would write into the temp checkout and vanish with the trap, a
   silent no-op that looks like success.
4. A recursion-guard env var so the new fixture's child invocation does not
   re-run the selftest forever.
5. **A selftest fixture that asserts the two paths DISAGREE.** This is the part
   that makes the fix non-rotting. The fixture commits a clean tree plus matching
   baseline, dirties the working copy so the two trees differ, and asserts BOTH
   that `--rev HEAD` sees the committed state AND that a working-tree scan of the
   same directory sees the dirty state. A `--rev` that silently fell back to the
   checkout fails the fixture. Verified by injecting exactly that rot and
   confirming the selftest goes rc=2.
6. Manifest row and dispatch arm move together, in one commit.

### How to prove a new fixture actually discriminates

A fixture that only catches a CRASH is worthless — the regression being guarded
against is silent, not loud. Inject the rot in its real shape: leave
materialisation succeeding and point the scan paths back at the working
checkout, then confirm the selftest fails with the fixture's own message.
Measured for the three gates converted so far:

```
=== type-walk fixture 7 ===                  (rot: MAT/PROJ/ALLOW resolved against $ROOT)
clean selftest rc=0
rotted selftest rc=2
  selftest: fixture 7 --rev did not read committed content: FAIL — 6 constructor(s) checked; unprojected and unallowlisted: Brandnew
restored rc=0

=== no-mock-fs-io fixture 6 ===              (rot: SCAN_ROOT="$ROOT" after a successful archive)
clean rc=0
rotted rc=1
  selftest FAIL: --rev did not read committed content, got [FAIL — 2 import site(s) checked, 1 new]
restored rc=0

=== runtime-source-list-parity fixture 8 ===  (rot: ROOT="$GIT_ROOT" after a successful archive)
clean selftest rc=0
rotted selftest rc=2
  selftest FAIL: --rev did not read committed content (exit 1): FAIL — 3 file(s) checked, 1 offender(s) (1 changed, 0 new, 0 stale-baseline, 0 stale-roster): b.c
restored rc=0
```

Note the rotted runs produce a real wrong-tree VERDICT (`FAIL — Brandnew`,
`FAIL — 1 new`, `FAIL — b.c`) rather than an error — that is exactly the shape
that slipped past everyone on 2026-09-06, and it is what the fixtures now catch.

### There are TWO rot axes, and a fixture must catch both

`--rev` has two independently rottable halves: the SCAN ROOT and the
BASELINE/ALLOWLIST. A fixture that dirties only the sources cannot see the
baseline half regress. Inject the second axis separately — leave `SCAN_ROOT` on
the rev and let the baseline path resolve against the working copy:

```
=== no-mock-fs-io: baseline reverts to working copy ===
rotted rc=1
  selftest FAIL: --rev did not read committed content, got [FAIL — 1 import site(s) checked, 1 stale]

=== type-walk: allowlist reverts to working copy ===
rotted rc=2
  selftest: fixture 7 --rev did not read committed content: FAIL — 6 constructor(s) checked; unprojected and unallowlisted: Brandnew

=== rt-src-list: baseline reverts to working copy ===
rotted rc=0        <-- MISSED IT
```

**`check-runtime-source-list-parity.shs` fixture 8 failed this test as first
written** and was strengthened before landing: it dirtied only the rosters, so
the working copy's baseline was byte-identical to the committed one and the rot
was invisible. It now also appends a row naming a nonexistent file to the
working copy's baseline, so a baseline-half regression surfaces as a
stale-baseline offender. After the fix:

```
=== rt-src-list: baseline reverts to working copy ===
rotted rc=2
  selftest FAIL: --rev did not read committed content (exit 1): FAIL — 3 file(s) checked, 1 offender(s) (0 changed, 0 new, 1 stale-baseline, 0 stale-roster): zz_not_a_real_file.c
```

### Injections measured 2026-09-07 for the three rows converted that day

```
=== port-io-single-owner, axis 1 (scan root -> checkout) ===
rotted rc=2
  selftest: fixture 4 --rev did not read committed content, got [FAIL — 2 declaring file(s) checked, 1 must not declare rt_port_* externs]
  axis 2: N/A — this guard has no baseline and no allowlist file (stated in the script header)

=== interpreter-extern-registry-gap, axis 1 (scan root -> checkout, baseline still from rev) ===
rotted rc=2
  selftest rev-reads-committed-content  FAIL(... FAIL — 3 symbol(s) checked, 1 new, 0 stale — new: rt_zz )
=== interpreter-extern-registry-gap, axis 2 (baseline -> checkout, scan root still the rev) ===
rotted rc=2
  selftest rev-reads-committed-content  FAIL(... FAIL — 2 symbol(s) checked, 0 new, 1 stale — stale: rt_nonexistent )

=== no-direct-rt, axis 1 (scan root -> checkout) ===
rotted rc=2
  ERROR — selftest failed: --rev did not read committed content, got [FAIL — forbidden direct rt_* count 2 exceeds baseline 1 (roots=src, src=2), extern_decls=0; top offenders: src/lib/two.spl:1 src/lib/one.spl:1 ]
=== no-direct-rt, axis 2 (baseline -> checkout) ===
rotted rc=2
  ERROR — selftest failed: --rev did not read committed content, got [PASS — 1 file(s) scanned (roots=src, src=1), forbidden=1, extern_decls=0 (baseline 9)]
=== no-direct-rt, axis 2b (ALLOWLIST -> checkout) ===
rotted rc=2
  ERROR — selftest failed: --rev did not read committed content, got [PASS — 1 file(s) scanned (roots=src, src=0), forbidden=0, extern_decls=0 (baseline 1)]
```

```
=== c-runtime-compiles, axis 1 (scan root + include path -> checkout) ===
rotted rc=2
  FAILING FIXTURES: fixture12_rev_did_not_read_committed_content(got=[FAIL — 1 file(s) failed to compile: src/runtime/fx_r_broken.c (2 compiled clean, 0 skipped ...)]) fixture13_incomplete_scope_not_fail_closed(got=[PASS — 1 file(s) compiled, 0 errors ...])
=== c-runtime-compiles, axis 2 (SKIP classifier's in-repo header lookup -> checkout) ===
rotted rc=2
  FAILING FIXTURES: fixture12_rev_did_not_read_committed_content(got=[FAIL — 1 file(s) failed to compile: src/runtime/fx_r_needs.c (1 compiled clean, 0 skipped ...)])
```

```
=== sffi-v2-authority, axis 1 (ROOT not repointed) ===
rotted rc=2
  selftest --rev did not read committed content, got [FAIL — 2 of 2 guard(s) failed]
=== sffi-v2-authority, axis 2 (sources from the rev, sub-guard SCRIPTS from the checkout) ===
rotted rc=2
  selftest --rev did not read committed content, got [FAIL — 2 of 2 guard(s) failed]
```

```
=== guard-wiring, axis 1 (SCAN_ROOT not repointed) ===
rotted rc=2
  SELFTEST FAILED: --rev enumerates only committed guards (expected 'guard_total=320', got 'guard_total=321')
  SELFTEST FAILED: --rev sees no NEW unwired (expected 'guard_unwired_new=0', got 'guard_unwired_new=2')
=== guard-wiring, axis 2 (BASELINE reverts to the checkout) ===
rotted rc=2
  SELFTEST FAILED: --rev does not read the working copy's baseline (expected 'no', got 'yes')
=== guard-wiring, axis 2b (OPT-OUT reverts to the checkout) ===
rotted rc=2
  SELFTEST FAILED: --rev sees no NEW unwired (expected 'guard_unwired_new=0', got 'guard_unwired_new=1')
```

Note each injection fires a DIFFERENT assertion — the fixture discriminates
between the three inputs rather than collapsing them into one "something is
wrong" signal.

**A wrapper-of-guards has a rot axis no data-file gate has: the sub-guard
SCRIPTS are themselves content.** A conversion that materialises the sources
the children read but still executes the children from the working copy — or
merely changes the cwd and lets their own `$0` resolve back to the checkout —
is still a wrong-tree verdict, and a sabotaged working-copy child would decide
the result. `check-sffi-v2-authority.shs`'s fixture injects exactly that
(axis 2 above: the committed marker is intact, only the child script is
sabotaged in the working copy).

**A materialising conversion has a third failure mode the two axes do not
name: an INCOMPLETE archive.** It does not produce a FAIL, it produces a
quieter PASS — files drop out of the compiled set into "skipped for an
unavailable external dependency" and the verdict still says PASS. Caught here
only by diffing the skip lists between the two paths. Any conversion that
materialises a SUBSET of the tree must diff its per-file classification
against the working-tree run before landing, and should fail closed on a
reference that escapes the archived scope (`check-c-runtime-compiles-push.shs`
fixture 13 is the worked example).

Note the shape of the two `no-direct-rt` axis-2 rots: both produce a **PASS**,
not an error — a silently wrong read of the ratchet's own floor. That is the
`rt-src-list` failure mode this section was written about, and it is now caught.

**A ratchet can have MORE than two rot axes.** `no-direct-rt` has three,
because its verdict depends on two separate data files (baseline and
allowlist), and a conversion that moves one and not the other is still wrong.
Count the data inputs before writing the fixture; "two axes" is a floor, not a
specification.

**Every future conversion must run BOTH injections.** A fixture proven on one
axis is proven on one axis. (`type-walk` fixture 7 dirties only the allowlist,
so its sources half rests on the real-repo tree-vs-rev comparison rather than on
the fixture — weaker, and stated here rather than glossed.)

## The 24 rows

`B` = push_blocking. Status as of this commit.

| # | row id | script | B | decision | status |
|---|--------|--------|---|----------|--------|
| 1 | `push-ui-slim-closure` (dup of 17) | `check-ui-slim-closure.shs` | no | duplicate row, delete | **DONE** |
| 2 | `push-ui-slim-closure-tui-entry` | `check-ui-slim-closure.shs` | no | `--rev` (import-closure over `.spl` source text) — blocked: needs the bootstrap seed to compute deps | TODO |
| 3 | `push-ui-slim-closure-cli-entry` | `check-ui-slim-closure.shs` | no | as above | TODO |
| 4 | `push-ui-slim-pack-inventory` | `check-ui-slim-pack-inventory.shs` | no | `--rev`; also needs `config/ui/pack_prefixes.sdn` from the rev | TODO |
| 5 | `push-c-runtime-compiles` | `check-c-runtime-compiles-push.shs` | **yes** | **materialise + `--rev`** (implemented inside the script, not in the dispatcher, so it is fixture-testable). Include paths and the SKIP classifier's in-repo header lookup both derive from the scan root, so repointing it moves them together — that is the second rot axis and fixture 12 injects it. **Trap found and closed here: `src/runtime` is NOT self-contained.** Two owned TUs reach out of it (`src/compiler/70.backend/.../simple_backend_plugin_v1.h`, `tools/counterpart/sdk/c/simple_counterpart_abi.h`), so archiving only `src/runtime` silently turned **130 compiled / 5 skipped into 128 / 7** — a coverage loss wearing a PASS. Fixed by also archiving `':(glob)src/**/*.h'` and `':(glob)tools/**/*.h'` (separate tolerant `git archive` invocations: one no-match pathspec fails the WHOLE archive), and fixture 13 now FAILS CLOSED when any escaping relative include resolves to something present in the revision but absent from the materialised tree. | **DONE 2026-09-07** |
| 6 | `push-no-direct-rt` | `check-no-direct-rt.shs --roots src` | **yes** | `--rev` over `':(glob)<root>/**/*.spl'` for each `--roots` entry, plus `no_direct_rt_baseline.txt` and `no_direct_rt_allowlist.txt` from the rev. Implemented by relocating `ROOT` itself, since `ALLOWLIST` and `BASELINE_FILE` are both derived from it — so all three inputs move together and cannot drift apart. **THREE rot axes here, not two**: scan root, baseline, and allowlist; fixture 17 injects all three and each was verified caught (below). Measured at conversion: the working checkout scanned 16342 `.spl` where the commit has 16318 — 24 untracked files the gate was counting and no push contained. | **DONE 2026-09-07** |
| 7 | `push-guard-wiring` | `check-guard-wiring.shs` | **yes** | `--rev`, and it IS a split after all — the census's "no split needed" line contradicted its own next clause. The wiring graph moves to the revision; `scan_installed_hooks` stays on the real repository root, because "is a hook installed in THIS clone, resolving to tracked current source" is a property of the machine. The `git ls-tree` design was not needed either: enumeration is `find "$_root/scripts/check"` etc., not `git ls-files`, so a materialised tree works as-is and only `SCAN_ROOT`/`OPTOUT`/`BASELINE` had to move. (`git ls-files` appears only inside `scan_installed_hooks`, the half that keeps the real root.) **THREE content inputs, each rot-injected separately and caught**: sources, frozen baseline, opt-out. Materialisation is `scripts .github src bin tools config` minus vendor, 312 MB / 1.2s, and every structured counter — `dead_dispatch_arms` included, so the four dead arms this guard credits are still credited — is byte-identical between the two paths. Gate cost 30.6s -> 32.2s. `MIN_GUARDS=300` was deliberately NOT made overridable: the fixture generates 320 real guard files rather than opening a seam a production run could use to lower the vacuity bound. | **DONE 2026-09-07** |
| 8 | `push-sosix-capsule-boundaries` | `check-sosix-capsule-boundaries.shs` | no | `--rev`; small (105 lines), accepts `--root` | TODO |
| 9 | `push-perf-regression-tests` | `check-perf-regression-tests.shs` | no | `--rev` over source text | TODO |
| 10 | `push-process-wait-eintr-retry` | `check-process-wait-eintr-retry.shs` | no | `--rev`; small (91 lines) | TODO |
| 11 | `push-interpreter-extern-registry-gap` | `check-interpreter-extern-registry-gap.shs --scan-only` | **yes** | `--rev` over `':(glob)src/compiler/**/*.spl'` + `interpreter_extern/mod.rs` + the frozen baseline. The baseline path was previously resolved from `repo_root` and so did **not** follow `--root`; it now resolves against the scanned tree, which is what makes the second rot axis coverable at all. Fixture 7 injects both axes. No longer red at origin/main (repaired by another lane). Caveat recorded: the push row's `--scan-only` skips the selftest, so the fixture is enforced by the separate bootstrap-tier row `interpreter-extern-registry-gap-selftest`, not on the push path — the same is true of `push-type-walk-constructor-parity`. | **DONE 2026-09-07** |
| 12 | `push-sffi-v2-authority` | `check-sffi-v2-authority.shs` | **yes** | **The census's provisional design was wrong on two counts and both were measured before writing code.** (a) A detached worktree is NOT required: `grep -lE '(^\|[^a-z])git ' scripts/audit/*sffi*.shs scripts/audit/rt-time-contract.shs` returns **0 files** — none of the 46 runs git — so `git archive` suffices and no shared `.git/worktrees/` state is written on a box with ~20 concurrent pushing sessions. (b) "run the wrapper with cwd inside `$WORK`" would NOT have worked: all 46 resolve their root from their own `$0` (234 hits for `cd -- "$(dirname -- "$0")/../.."`, zero `rev-parse --show-toplevel`), so the wrapper must execute the COPIES INSIDE the materialised tree. Repointing `ROOT` does both halves, since `run_guard` already invokes `sh "$ROOT/$guard_rel"`. Scope `src scripts test examples` minus the vendored trees: 551 MB / 3.3s, vs 2.0 GB / 19s with vendor, and verified not to change any of the 46 verdicts. Gate cost 29s -> 41s. Gained its first selftest (3 fixtures, `--guard-list` drives the real loop over 2 fakes). **STILL RED — 3 of 46, identically on the checkout and on the revision, so it is real committed debt.** | **DONE 2026-09-07** |
| 13 | `push-type-walk-constructor-parity` | `check-type-walk-constructor-parity.shs --scan-only` | **yes** | `--rev` — reads exactly 3 files | **DONE** |
| 14 | `push-shs-path-conversion-equivalence` | `check-shs-path-conversion-equivalence.shs` | no | scan half is source text → `--rev`. The *exec* half needs `cygpath` and is NOT RUN off Windows; that half is genuinely host-scoped. | TODO (split) |
| 15 | `push-shs-native-tool-boundary-preserved` | `check-shs-native-tool-boundary-preserved.shs` | no | as above | TODO (split) |
| 16 | `push-dual-run-shadow` | `check-dual-run-shadow.shs` | no | **not** "correct as-is": it needs a runnable `bin/simple`, so it is *blocked on a rev-built binary*, not tree-scoped by nature. Do not misfile it. | TODO (blocked) |
| 17 | `push-ui-slim-closure` | `check-ui-slim-closure.shs` | no | see 2 | TODO |
| 18 | `push-parser-source-global-ratchet` | `check-parser-source-global-ratchet.shs` | no | `--rev`; small (136 lines), accepts `--root` | TODO |
| 19 | `push-rt-api-groups` | `check-rt-api-groups.shs` | no | `--rev` plus `config/api/api_registry.sdn` and `rt_api_group_baseline.txt` from the rev; needs `rg` | TODO |
| 20 | `push-runtime-source-list-parity` | `check-runtime-source-list-parity.shs` | **yes** | `--rev` over `src/runtime` plus the three roster files AND the baseline | **DONE** |
| 21 | `push-no-mock-file-system-io` | `check-no-mock-file-system-io.shs` | **yes** | `--rev` | **DONE** |
| 22 | `push-lifecycle-reachability` | `check-lifecycle-reachability.shs` | no | `--rev`; accepts `--root` | TODO |
| 23 | `push-plan-acceptance-swept` | `check-plan-acceptance-swept.shs` | no | needs a runnable Simple binary — blocked, like 16, not tree-scoped by nature | TODO (blocked) |
| 24 | `push-local-ci-receipt-selftest` | `verify-local-ci-receipt.shs --selftest` | no | **genuinely correct as a tree row, with a caveat.** `--selftest` exercises the verifier's own fixtures; it asserts a property of the SCRIPT, not of repository content. But the script it exercises should be the pushed one, so the honest form is still "materialise the rev and run its `--selftest`". Left as-is for now and documented here so the next reader does not assume it was overlooked. | LEAVE (documented) |

**The "genuinely tree-scoped" bucket is very nearly empty.** Only the
installed-hook half of `push-guard-wiring` (row 7) and the `cygpath`-exec halves
of rows 14/15 are truly properties of the pushing machine rather than of the
pushed commit. Everything else is a property of the commit and belongs on `--rev`.
"Needs a runnable binary" (16, 23) is a *blocker*, not a justification.

## Rows added after the original table

| row id | script | B | decision | status |
|---|---|---|---|---|
| `push-port-io-single-owner` | `check-port-io-single-owner.shs` | **yes** | `--rev` over `src/os` (whole directory, not a `*.spl` glob — the scan is content-based, so a `.c`/`.S` declarer must stay visible). **No baseline or allowlist file exists for this guard**, so the census's second rot axis has no surface; fixture 4 covering the scan root is the COMPLETE form here, not the weak one-axis form. Stated in the script header and the manifest description so nobody "strengthens" it wrongly. | **DONE 2026-09-07** |
| `push-rt-api-groups` (dup) | `check-rt-api-groups.shs` | no | duplicate row, delete (kept the fuller description at line 32) | **DONE 2026-09-07** |
| `push-rt-api-groups` | `check-rt-api-groups.shs` | no | `--rev` plus `config/api/api_registry.sdn` and `rt_api_group_baseline.txt` from the rev; needs `rg` | TODO |

## Blocking gates found RED on a pristine checkout

Measured 2026-09-06 in a clean worktree at `506601075df`, before any edit, all
8 blocking `tree`-mode rows run as-is:

```
c-runtime-compiles         rc=0 PASS — 130 file(s) compiled, 0 errors (5 skipped for unavailable external dependencies)
extern-registry-gap        rc=1 FAIL — 234 symbol(s) checked, 2 new, 0 stale — new: rt_file_publish_noreplace rt_secure_temp_dir
guard-wiring               rc=0 PASS — 1593 guard(s) checked, 429 invoked, 0 NEW unwired
no-direct-rt               rc=0 PASS — 16339 file(s) scanned (roots=src, src=6206), forbidden=6206 (baseline 7776)
no-mock-fs-io              rc=0 PASS — 9 import site(s) checked, 0 new, 0 stale
runtime-source-list-parity rc=0 PASS — 135 file(s) checked, 0 drift
sffi-v2-authority          rc=1 FAIL — 12 of 46 guard(s) failed
type-walk                  rc=0 PASS — 12 constructor(s) checked, 0 unprojected and unallowlisted
```

A side observation from the same run, not a red but worth one line:
`no-direct-rt` reports `forbidden=6206 (baseline 7776)` — the population is
**1,570 sites BELOW its own baseline**. A ratchet sitting 20% under its floor has
stopped ratcheting: 1,570 new forbidden call sites could land before it noticed.
Ratcheting the baseline down to the measured value is a separate, reviewed
change (`--generate-baseline` after reading the diff), deliberately not made
here.

### Re-measured 2026-09-07 at `60479fbf013`, clean worktree, before any edit

```
port-io-single-owner       rc=0 PASS — 1 declaring file(s) checked, all rt_port_* externs confined to src/os/kernel/arch/x86/port_io_owner.spl
extern-registry-gap        rc=0 PASS — 234 symbol(s) checked, 0 new, 0 stale        <-- REPAIRED since 2026-09-06
guard-wiring               rc=0 PASS — 1596 guard(s) checked, 431 invoked, 1145 orphaned (734 baselined as known unwired debt, rest justified), 0 NEW unwired, 0 copied hook(s)
no-direct-rt               rc=0 PASS — 16342 file(s) scanned (roots=src, src=6072), forbidden=6072, extern_decls=6455 (baseline 7776)
c-runtime-compiles         rc=0 PASS — 130 file(s) compiled, 0 errors (5 skipped for unavailable external dependencies)
sffi-v2-authority          rc=1 FAIL — 3 of 46 guard(s) failed                      <-- STILL RED, improved from 12
```

So **one** blocking gate is red on `main` now, not two: the extern-registry-gap
red was repaired by another lane, and `sffi-v2-authority` went 12 → 3. The
`no-direct-rt` under-baseline observation below is worse, not better: it now
measures **6072 against a baseline of 7776**, 1,704 sites of unused headroom.

**Two BLOCKING push gates are red on `main` itself**, in a clean checkout, with
no local edits to blame:

- `push-interpreter-extern-registry-gap` — 2 new unbacked symbols,
  `rt_file_publish_noreplace` and `rt_secure_temp_dir`.
- `push-sffi-v2-authority` — 12 of 46 audit guards failing.

Neither was introduced by the wrong-tree work and neither is fixed here. They are
the reason pushes are routinely made with `--no-verify`, and `--no-verify`
nullifies every gate in the manifest — which is precisely the condition that let
the 2026-09-06 incident land. **Fixing the wrong-tree defect does not help while
two blocking gates are red on `main`**; the two efforts have to meet.

A third red was observed transiently and self-resolved: `check-guard-wiring`
went `FAIL — 1 NEW unwired` naming `scripts/check/gen-stdlib-api-registry.shs`
(added by `7a4556c1247`) and was green again two fetches later once another lane
landed the opt-out entry. Worth noting only as evidence of how fast `main`
churns: an agent must re-fetch and re-run rather than trusting a verdict from
minutes earlier.

## What is left undone

### As of 2026-09-07: 15 `tree`-mode push rows remain, and **none of them is blocking**

All six blocking rows are converted, and

```sh
awk -F', ' '/^    [a-z]/ {gsub(/^ +/,"",$1); if($2=="push" && $4=="tree" && $3=="true") print $1}' \
  config/check/must_check_gates.sdn
```

returns nothing. The push tier now reads **15 tree / 13 ref / 6 range**
(from 22 / 7 / 5 at the start of the day: −6 tree rows converted to `ref`, −1
duplicate tree row removed; the extra `range` row is `push-merge-content-
conservation`, landed by another lane the same day and unrelated to this work).
Re-derive with:

```sh
awk -F', ' '/^    [a-z]/ {gsub(/^ +/,"",$1); if($2=="push") print $4}' \
  config/check/must_check_gates.sdn | sort | uniq -c
```

Per-row plan for the 15, all advisory (`push_blocking=false`):

| row id | plan | note |
|---|---|---|
| `push-ui-slim-closure` | `--rev` | blocked: computes the import closure with the bootstrap seed |
| `push-ui-slim-closure-tui-entry` | `--rev` | same blocker |
| `push-ui-slim-closure-cli-entry` | `--rev` | same blocker |
| `push-ui-slim-pack-inventory` | `--rev` | also needs `config/ui/pack_prefixes.sdn` from the rev; same seed blocker. Its dispatch arm additionally lacks the `\|\| { rm -f; return 1; }` tail every other arm has — harmless while advisory, fix it with the conversion |
| `push-sosix-capsule-boundaries` | `--rev` | small (105 lines), accepts `--root` |
| `push-perf-regression-tests` | `--rev` | source text; RED on main (4 regressed), advisory |
| `push-process-wait-eintr-retry` | `--rev` | small (91 lines); its own selftest is RED on main |
| `push-shs-path-conversion-equivalence` | split: `--rev` for the scan half | the `cygpath` EXEC half is genuinely host-scoped and NOT RUN off Windows |
| `push-shs-native-tool-boundary-preserved` | split, as above | same |
| `push-dual-run-shadow` | **BLOCKED** on a rev-built `bin/simple` | not tree-scoped by nature; do not misfile it |
| `push-parser-source-global-ratchet` | `--rev` | small (136 lines), accepts `--root` |
| `push-rt-api-groups` | `--rev` | plus `config/api/api_registry.sdn` and `rt_api_group_baseline.txt` from the rev; needs `rg`. Two data files, so THREE rot axes like `no-direct-rt` |
| `push-lifecycle-reachability` | `--rev` | accepts `--root` |
| `push-plan-acceptance-swept` | **BLOCKED** on a runnable Simple binary | not tree-scoped by nature |
| `push-local-ci-receipt-selftest` | materialise + run the rev's `--selftest` | it asserts a property of the SCRIPT, but it should be the PUSHED script |
| (`push-ui-slim-closure` dup) | — | already removed |

Two blockers are shared and worth stating once: rows needing the bootstrap seed
or a runnable `bin/simple` cannot be converted until a rev-built binary exists.
That is a BLOCKER, not a justification for tree mode.

### RED found while converting, NOT caused by the conversion (2026-09-07)

`check-guard-wiring` is FAILING at `origin/main` content:

```
check-guard-wiring: FAIL — 1598 guard(s) checked, 1 NEW unwired (725 baselined as known debt), 0 stale/bad baseline or opt-out line(s), 0 copied hook(s)
  unwired_guard=check-llm-caret-server-serves.shs
```

Attribution, so nobody wastes time on the wrong lane: that guard was added by
`398665ef526` (PR #433, "make the caret demo server actually serve"), a
different lane, and it is wired into nothing. The verdict is **identical on the
working checkout and on `--rev origin/main`**, which is itself evidence the
conversion is faithful — a conversion that had broken the scan would make the
two disagree. Nothing was adjusted to hide it: the baseline was NOT
regenerated, and the guard was NOT added to the opt-out. The repair belongs to
whoever owns `check-llm-caret-server-serves.shs` — wire it into a workflow or
write an opt-out line with a reason.

This is a BLOCKING row, so until it is repaired the pre-push hook has a second
reason to end in failure, alongside `push-sffi-v2-authority`.

### Still true, and still the thing that bounds all of this

`push-sffi-v2-authority` is red (3 of 46) on the revision as well as on the
checkout, so the pre-push hook still ends `BLOCKING gate push-sffi-v2-authority
failed` on an unmodified tree and topic pushes are still made with
`--no-verify`, which skips the dispatcher and every row in it. These gates now
read the right tree *when they run*; on the current landing path they do not
run.
