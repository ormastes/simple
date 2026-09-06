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
Measured for the two gates converted so far:

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
```

Note both rotted runs produce a real wrong-tree VERDICT (`FAIL — Brandnew`,
`FAIL — 1 new`) rather than an error — that is exactly the shape that slipped
past everyone on 2026-09-06, and it is what the fixtures now catch.

## The 24 rows

`B` = push_blocking. Status as of this commit.

| # | row id | script | B | decision | status |
|---|--------|--------|---|----------|--------|
| 1 | `push-ui-slim-closure` (dup of 17) | `check-ui-slim-closure.shs` | no | duplicate row, delete | **DONE** |
| 2 | `push-ui-slim-closure-tui-entry` | `check-ui-slim-closure.shs` | no | `--rev` (import-closure over `.spl` source text) — blocked: needs the bootstrap seed to compute deps | TODO |
| 3 | `push-ui-slim-closure-cli-entry` | `check-ui-slim-closure.shs` | no | as above | TODO |
| 4 | `push-ui-slim-pack-inventory` | `check-ui-slim-pack-inventory.shs` | no | `--rev`; also needs `config/ui/pack_prefixes.sdn` from the rev | TODO |
| 5 | `push-c-runtime-compiles` | `check-c-runtime-compiles-push.shs` | **yes** | **materialise + `--root`** — it must feed real `.c`/`.h` files to `clang -fsyntax-only`. Already accepts `--root`, so the dispatch change is `git archive <rev> -- src/runtime` into a temp dir and pass it. Include paths must resolve inside the materialised tree. | TODO |
| 6 | `push-no-direct-rt` | `check-no-direct-rt.shs --roots src` | **yes** | `--rev` over `':(glob)src/**/*.spl'` plus `no_direct_rt_baseline.txt` and `no_direct_rt_allowlist.txt` from the rev. Already accepts `--root`. Largest single win after the two below. | TODO |
| 7 | `push-guard-wiring` | `check-guard-wiring.shs` | **yes** | `--rev`. Design settled, no split needed: the guard ENUMERATION switches from `git ls-files` to `git ls-tree -r --name-only $REV --` (a `git archive` extraction has no `.git`, so `ls-files` there returns nothing — fail-closed, but broken), while the installed-hook check stays on the working machine, since "is the hook installed here" really is a property of this host. One script, `--rev` gating one loop. | TODO |
| 8 | `push-sosix-capsule-boundaries` | `check-sosix-capsule-boundaries.shs` | no | `--rev`; small (105 lines), accepts `--root` | TODO |
| 9 | `push-perf-regression-tests` | `check-perf-regression-tests.shs` | no | `--rev` over source text | TODO |
| 10 | `push-process-wait-eintr-retry` | `check-process-wait-eintr-retry.shs` | no | `--rev`; small (91 lines) | TODO |
| 11 | `push-interpreter-extern-registry-gap` | `check-interpreter-extern-registry-gap.shs --scan-only` | **yes** | `--rev`; accepts `--root`. **RED at origin/main — see below.** | TODO |
| 12 | `push-sffi-v2-authority` | `check-sffi-v2-authority.shs` | **yes** | 102-line wrapper over 46 separate `scripts/audit/*.shs` guards with **zero selftest**. Per-script `--rev` is infeasible, but the fix is still one commit: `git worktree add --detach $WORK $REV` then run the wrapper with cwd inside `$WORK`. A detached worktree (not `git archive`) is required precisely because the 46 sub-guards may run git themselves. Add the missing selftest in the same change — a 46-guard wrapper with no fixtures cannot be shown to discriminate at all. **RED at origin/main — see below.** | TODO |
| 13 | `push-type-walk-constructor-parity` | `check-type-walk-constructor-parity.shs --scan-only` | **yes** | `--rev` — reads exactly 3 files | **DONE** |
| 14 | `push-shs-path-conversion-equivalence` | `check-shs-path-conversion-equivalence.shs` | no | scan half is source text → `--rev`. The *exec* half needs `cygpath` and is NOT RUN off Windows; that half is genuinely host-scoped. | TODO (split) |
| 15 | `push-shs-native-tool-boundary-preserved` | `check-shs-native-tool-boundary-preserved.shs` | no | as above | TODO (split) |
| 16 | `push-dual-run-shadow` | `check-dual-run-shadow.shs` | no | **not** "correct as-is": it needs a runnable `bin/simple`, so it is *blocked on a rev-built binary*, not tree-scoped by nature. Do not misfile it. | TODO (blocked) |
| 17 | `push-ui-slim-closure` | `check-ui-slim-closure.shs` | no | see 2 | TODO |
| 18 | `push-parser-source-global-ratchet` | `check-parser-source-global-ratchet.shs` | no | `--rev`; small (136 lines), accepts `--root` | TODO |
| 19 | `push-rt-api-groups` | `check-rt-api-groups.shs` | no | `--rev` plus `config/api/api_registry.sdn` and `rt_api_group_baseline.txt` from the rev; needs `rg` | TODO |
| 20 | `push-runtime-source-list-parity` | `check-runtime-source-list-parity.shs` | **yes** | `--rev` over `src/runtime` plus the three roster files; accepts `--root` | TODO |
| 21 | `push-no-mock-file-system-io` | `check-no-mock-file-system-io.shs` | **yes** | `--rev` | **DONE** |
| 22 | `push-lifecycle-reachability` | `check-lifecycle-reachability.shs` | no | `--rev`; accepts `--root` | TODO |
| 23 | `push-plan-acceptance-swept` | `check-plan-acceptance-swept.shs` | no | needs a runnable Simple binary — blocked, like 16, not tree-scoped by nature | TODO (blocked) |
| 24 | `push-local-ci-receipt-selftest` | `verify-local-ci-receipt.shs --selftest` | no | **genuinely correct as a tree row, with a caveat.** `--selftest` exercises the verifier's own fixtures; it asserts a property of the SCRIPT, not of repository content. But the script it exercises should be the pushed one, so the honest form is still "materialise the rev and run its `--selftest`". Left as-is for now and documented here so the next reader does not assume it was overlooked. | LEAVE (documented) |

**The "genuinely tree-scoped" bucket is very nearly empty.** Only the
installed-hook half of `push-guard-wiring` (row 7) and the `cygpath`-exec halves
of rows 14/15 are truly properties of the pushing machine rather than of the
pushed commit. Everything else is a property of the commit and belongs on `--rev`.
"Needs a runnable binary" (16, 23) is a *blocker*, not a justification.

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

Rows 2-12 and 14-23 above. Each needs its own commit carrying its own
discriminating fixture; batching them into one infrastructure commit risks
breaking the dispatcher for every session on the box, which is a strictly worse
outcome than a slow migration. Rows 7 and 12 additionally need a design decision
(split, and detached-worktree respectively) before anyone writes code.
