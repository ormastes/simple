# Local CI receipt — operator guide

**Audience:** a developer who wants their PR's required
`Code Idiom & Structural Ratchet Gates` context to take a fast path instead of
re-running 27 gate scripts on a saturated runner queue.

**Status, PR #416 branch `ci-receipt-signed-sanity-2026-09-06`:** the signer, the
verifier, the allowed-signers trust root and the mode decision in
`repo-hygiene.yml` have all landed, and the path works end to end **locally**.
Verified on `c70a818a0`, a commit with **no** change-id header: sign exit 0
binding `patch a251811056b6100759aab75b4863154ba3d3ad3f`, verify exit 0, tamper
exit 1. Selftests: verifier 25/25, signer 18/18.

Three things you must know before relying on it:

1. **Delivery is a manual step.** CI reads the receipt from a git note on
   `refs/notes/ci-receipts`, and `sign-local-ci-receipt.shs` has **no
   note-emission flag** (`git notes` and `--note` occur zero times in it). You
   attach and push the note yourself — §7. This is the top usability gap.
2. **`config/check/ci_receipt_allowed_signers` ships with ZERO keys**, so
   nothing is admitted until a key is deliberately added — §5.
3. **The fast path has never been exercised on a CI runner.** Every result above
   is local. Nothing here is runner-proven.

Specification: `doc/05_design/infra/local_ci_receipt/design.md`.
Order of work and acceptance bars: `doc/03_plan/infra/local_ci_receipt/plan.md`.
Measured motivation: `doc/01_research/infra/local_ci_receipt/local_ci_receipt_and_signing_2026-09-06.md`.

---

## 1. Why this exists (measured, not motivational)

`main` is not branch-protected. Enforcement is the ruleset `spipe-vcs-v3-main`,
which requires exactly two status contexts:

- `Code Idiom & Structural Ratchet Gates` (job `code-idiom-gates` in
  `.github/workflows/repo-hygiene.yml`)
- `SPipe Self Review Admission`

The idiom context **never succeeds on a pull request.** Last 60 runs of
`repo-hygiene.yml`, split by event, measured 2026-09-06:

| event | outcome | count |
|---|---|---|
| pull_request | cancelled | 31 |
| pull_request | queued, never started | 24 |
| pull_request | failure | 4 |
| push | failure | 1 |

**Zero successes.** The mechanism is a loop between two policies, not slowness:

1. The ruleset requires branches to be up to date, so a PR rebases whenever
   `main` advances — measured at 162 commits/24 h, roughly one every **8.9 min**.
2. Each rebase force-pushes the head, firing `synchronize`, and
   `repo-hygiene.yml` declares `cancel-in-progress: true`, which kills the
   in-flight run.
3. Queue depth was 322 repo-wide against 5 in progress. The one success anywhere
   in recent history waited **2112 s queued** for **172 s of execution** — 92%
   queue.

Queue wait (~35 min) exceeds the rebase interval (~9 min), so a run is cancelled
and restarted before it is ever scheduled. It is not slow; it is **unreachable**.
Raising `cancel-in-progress: false` would only pile stale runs onto a saturated
queue. The only thing that closes the loop is a required-context run short enough
to finish between two rebases — the ~60 s `sanity` path.

("Unreachable" above describes **the required check as it runs today, without a
receipt.** It is not a statement about the receipt fast path, which works
locally; see the Status block.)

---

## 2. Trust class — read this before you rely on it

A dev-key signature proves **WHO produced the receipt, not THAT the gates ran.**

This is the same trust class as `review-admission.yml`'s `self_attestation`
input, whose own description in that workflow reads *"this is not independent
authentication"*. Nothing here is server-grade verification. There is
deliberately no `producer_id != reviewer_key_id` independence check (the one
`check-external-must-check-receipt.shs` has), because a local receipt is
self-attestation by construction: the producer and the signer are the same
person. Adding a field that always holds trivially would misrepresent the trust
class rather than raise it.

What CI still recomputes on the real head **before any row is skipped**:

- the sshsig signature and the allowed-signer check
- the identity set (kind and value) and the tree binding
- the manifest binding and the manifest↔receipt id-set cross-check
- the per-row status
- the conflict-class guards (conflict-tree, conflict-markers, tree-size) —
  **blocking in every mode**, gated only on `steps.receipt.outputs.range != ''`,
  which is set for every `pull_request` event; anything that leaves it empty is
  `full` by construction, where the gates themselves are the enforcement.
  Measured on a CI-shaped range: conflict-tree 1 s, conflict-markers 5 s,
  tree-size 2 s — 8 s, affordable inside the 60 s `sanity` budget. They matter
  because a receipt attests the tree
  the developer ran gates on while CI tests the **merge** of that head against a
  base that moves every few minutes. `main` was wiped to four files twice in 24 h
  with every other check green.

---

## 3. The modes

There is no binary skip. The decision is made by the `Local CI receipt
admission` step of `code-idiom-gates`, and it only ever *widens* trust — every
failure path returns with the mode still `full`.

The workflow's own header comment says "THREE MODES, and only three". **That
comment is stale: the landed code emits four**, having added `docs`. Read the
table, not the comment.

| mode | condition | what runs | budget |
|---|---|---|---|
| `docs` | receipt verifies **and** every changed path is documentation | the conflict-class floor only | ≤ 60 s |
| `sanity` | receipt verifies **and** the attested tree is the tree under test | receipt verify + conflict-tree + conflict-markers + tree-size | ≤ 60 s |
| `escalate` | receipt verifies for the PR head, but the merge CI is testing has a different tree | the sanity set, plus every gate whose declared `inputs` intersect the paths the merge changed. A gate whose `inputs` are `*` (unbounded) **always** runs | bounded by the diff |
| `full` | everything else, and every undecidable, missing, malformed, unsigned, mismatched or unreadable input | every gate, exactly as before | unchanged |

The fail-closed hinge is the **inverted** `if:` on each gate step:

```yaml
if: ${{ !cancelled() && (!contains(steps.receipt.outputs.skip_ids, '|ci-cpu-hotloop-idiom|')) }}
```

An empty, missing or unset `skip_ids` makes `contains` false, so the gate
**runs**. A decision step that dies, is skipped, or emits nothing therefore runs
everything. Nothing can be skipped by omission.

`sanity` additionally skips the `apt-get install ripgrep` step, because apt-get
alone costs more than the whole 60 s budget. That step's condition is
`steps.receipt.outputs.mode != 'sanity'`, so an empty output installs by default.

---

## 4. Generating a signing key

Use a key that signs **nothing else**. Reusing an existing SSH key means a
signature you made for some other purpose is one namespace check away from being
replayed as a CI receipt.

```bash
ssh-keygen -t ed25519 -C ci-receipt-<who> -f ~/.ssh/simple_ci_receipt
```

Requires OpenSSH ≥ 8.0 for `ssh-keygen -Y` (sshsig). Both scripts assert this
and **ERROR** rather than skipping when it is absent or unparseable.

```bash
ssh -V        # OpenSSH_10.3p1 measured locally; runners are well past 8.0
```

---

## 5. Getting your key into `config/check/ci_receipt_allowed_signers`

**The file ships with ZERO keys.** That is the intended fail-closed default: an
allowlist with no key admits nobody, every verification returns non-zero, and CI
therefore runs the full gate set. `verify-local-ci-receipt.shs` pins this — its
selftest case `c2` fails if the shipped file ever admits a signer. A receipt
feature that starts out trusting somebody is a receipt feature that starts out
broken.

Append exactly one line, key material taken verbatim from the `.pub` file:

```bash
printf '%s namespaces="simple-ci-receipt" %s\n' \
    <principal> "$(cut -d' ' -f1,2 ~/.ssh/simple_ci_receipt.pub)" \
    >> config/check/ci_receipt_allowed_signers
```

- `<principal>` is what you pass as `--identity` and what the verifier passes to
  `ssh-keygen -Y verify -I`. Both scripts constrain it to `[A-Za-z0-9._@+-]`; an
  email-shaped id is conventional.
- `namespaces="simple-ci-receipt"` is **mandatory**. Without it the key would be
  accepted for every sshsig namespace, so a signature you produced for an
  unrelated purpose (git commit signing, say) could be replayed as a CI receipt.

**Land that line through review on the BASE branch, in its own PR.** Two reasons,
both hard:

1. The allowed-signers file, the verifier script and the skip logic are read from
   `.ci-base` — a checkout of the PR's **base** sha — never from the PR head.
   Otherwise a PR could add its own key and sign its own receipt.
2. `decide()` refuses admission outright for any PR that touches
   `.github/workflows/`, `scripts/check/`, `scripts/hooks/` or `config/check/`:

   > `the PR edits check policy (<path>); a receipt may never admit its own rules`

   So **the PR that adds your key always runs `full` itself.** That is correct
   and not a bug to route around. Reviewers should reject a PR that adds a key in
   the same change whose gates that key would let it skip.

---

## 6. Running the local gates and minting a receipt

The receipt covers the **`ci` tier** of `config/check/must_check_gates.sdn` —
27 rows as of 2026-09-06, all with `ci_job` = `code-idiom-gates`. The manifest's
columns are:

```
must_check_gates |id, tier, push_blocking, mode, command, ci_job, inputs, description|
```

`ci_job` maps a row to the CI job that may skip it. `inputs` carries the path set
that `escalate` intersects against the rebase diff; `*` means unbounded, and an
unbounded gate always re-runs.

### 6a. Let the signer run the gates for you

```bash
sh scripts/check/sign-local-ci-receipt.shs \
    --key ~/.ssh/simple_ci_receipt \
    --identity <principal> \
    --tier ci \
    --run \
    --rev HEAD \
    --changes <base>..HEAD \
    --allowed-signers config/check/ci_receipt_allowed_signers
```

`--run` executes each manifest row's command from the repository root and derives
pass/fail from its exit status. It is slow, and **several rows need a deployed
full-CLI `bin/simple`** — which this repo's `bin/simple` is not on every host
(it is bootstrap-only on the mac lane, exposing `compile` and `native-build`
alone). Where that bites, use 6b.

### 6b. Supply verdicts you produced yourself

```bash
sh scripts/check/sign-local-ci-receipt.shs \
    --key ~/.ssh/simple_ci_receipt \
    --identity <principal> \
    --tier ci \
    --results /path/to/results.txt \
    --rev HEAD \
    --changes <base>..HEAD \
    --allowed-signers config/check/ci_receipt_allowed_signers
```

`--allowed-signers` is optional in both forms; when given, the freshly signed
receipt is verified against that file before the signer reports success. Pass it.

`results.txt` is one `<row-id> <status>` per line; blank lines and `#` comments
are ignored. **Its id set must equal the manifest's ids for the tier** — the
signer FAILs on drift in either direction.

Claim coverage only of rows you actually ran. Claimed-but-unrun coverage is the
one defect that makes this feature worse than not having it.

### What the signer does and does not decide

The signer records verdicts **faithfully**. It is not the gate: it will sign a
receipt containing a non-pass row, say so in its own verdict line, and exit 1.
The verifier decides admissibility. A signer that refused to record a failure
would quietly turn "the gates failed" into "no receipt exists", which is a weaker
statement.

### Other flags worth knowing

| flag | effect |
|---|---|
| `--out FILE` | receipt path; default `$SIMPLE_CI_RECEIPT_FILE` or `doc/08_tracking/check/local_ci_receipt.v1.txt`. The signature goes to `<out>.sig` |
| `--session-id ID` | default `$SIMPLE_SESSION_ID` or `local` |
| `--signed-at TS` | pin the timestamp. With `--session-id`, this is what makes two runs on identical state produce **byte-identical** payloads |
| `--root DIR` | repository root; default `git rev-parse --show-toplevel` |
| `--selftest` | fixtures; fatal, runs before every scan |

### Verify it locally before you push

```bash
sh scripts/check/verify-local-ci-receipt.shs \
    --rev HEAD --changes <base>..HEAD --tier ci \
    --allowed-signers config/check/ci_receipt_allowed_signers
```

This is the same invocation CI makes, so a local `PASS` is the strongest
pre-push signal available. Pass the **same** `--rev` and `--changes` CI will —
note CI splits the note back into two temp files and points `--receipt` and
`--signature` at them:

```
sh "$verifier" --root "$PWD" --rev "$HEAD_SHA" \
    --changes "$BASE_SHA..$HEAD_SHA" --tier ci \
    --receipt "$tmp/ci-receipt" --signature "$tmp/ci-receipt.sig" \
    --allowed-signers "$signers"
```

`--rev` is the **PR head, never the merge tip**: a GitHub merge commit has two
parents and `git patch-id` is undefined for a merge, so binding the tested merge
would be unbindable by construction.

Note the default `--tier` differs between the two scripts: the signer defaults to
`push`, the verifier defaults to the receipt's own `tier` field, and CI demands
`ci`. **Always pass `--tier ci` when signing for CI.**

---

## 7. Where the receipt goes — publish it as a git note (manual step)

CI reads the receipt from **a git note on `refs/notes/ci-receipts`, keyed by the
PR head sha**. It cannot be a tracked file: the receipt binds `tree`, so
committing it into that tree changes the tree, and the bound tree could never
equal the tested one. A note lives outside the commit tree, so attaching one
perturbs nothing.

**The signer does not do this for you.** `sign-local-ci-receipt.shs` has no
note-emission flag — `git notes` and `--note` occur zero times in it. It writes
`--out FILE` and `<out>.sig`, and stops. **This is the top usability gap in the
feature.** Until a `--note` flag lands, run these three commands yourself, from
the repo, after a successful sign:

```bash
cat doc/08_tracking/check/local_ci_receipt.v1.txt \
    doc/08_tracking/check/local_ci_receipt.v1.txt.sig > /tmp/note
git notes --ref=ci-receipts add -f -F /tmp/note <head-sha>
git push origin refs/notes/ci-receipts
```

Substitute your own `--out` path if you passed one. `<head-sha>` is the PR head
commit — the same sha CI passes as `--rev`, not the merge tip.

Notes on the mechanics:

- The note body is the concatenation `payload || signature`. CI splits it back
  apart on the **first line exactly equal to** `-----BEGIN SSH SIGNATURE-----`:
  everything strictly before is the payload, everything from that line on is the
  signature. `cat receipt sig` produces exactly that shape; do not reformat it.
- The note is author-writable, and that is fine. The sshsig signature inside it,
  checked against the **BASE** allowed-signers file, is what protects the
  contents.
- **A missing note is the ordinary case, not an error.** It means the PR carries
  no receipt, which means `full`. You will see
  `no refs/notes/ci-receipts on origin: this PR carries no receipt` or
  `no ci-receipt note on head <sha>`.
- Re-push the note after **every** rebase or amend: the head sha changes, so the
  old note no longer keys to anything CI looks up, and the tree changed too, so
  the old receipt would be `escalate` at best. Re-sign, then re-attach.

`design.md` §6.2 rejects the alternatives for reasons that still hold: a tracked
file is circular (§3.1); workflow artifacts are produced by CI rather than by the
developer and are attacker-controlled in the same trust position as the head
checkout; PR comments are mutable and Markdown mangles the exact bytes
`design.md` §4 depends on; a commit trailer changes the commit but says nothing
about the tree.

---

## 8. Telling which mode your PR got, and why

The decision step prints one greppable line into the job log:

```
LOCAL-CI-RECEIPT MODE: <mode> (<reason>)
```

Find it in the `Local CI receipt admission` step of the
`Code Idiom & Structural Ratchet Gates` job. The step also echoes the first 40
lines of the verifier's output, so the verifier's own verdict line is visible
there too. The default reason, before anything has been proved, is:

```
default: nothing has proved a receipt for this head
```

### Commit identity — two kinds, both supported

Both the signer and the verifier resolve a rebase-stable identity for every
commit in the `--changes` range, fail-closed at each step:

1. **`change <id>`** — the jj `change-id` header. jj writes it into the git
   commit object, so plain `git cat-file commit <sha>` reads it and no jj binary
   is needed. It survives rebase, amend and force-push.
2. **`patch <id>`** — `git show <sha> | git patch-id --stable`, for **non-merge**
   commits that carry no such header. A patch-id hashes the diff only, so it too
   survives rebase and cherry-pick.
3. Neither ⇒ **unbindable**, and both scripts FAIL. There is no third fallback:
   inventing one would make an unbindable commit look bound.

Why the fallback exists at all: **measured 2026-09-06, 0 of the last 40
`origin/main` commits and 0 of PR #380's head commits carry a change-id header.**
Commits reaching GitHub are GitHub merge commits or plain-git commits from this
repo's `git worktree add --detach` + `gh pr create` landing route, and neither
writes one. Without the patch-id kind the feature would never engage on a real
PR. Verified end to end on `c70a818a0`, which has no change-id header: sign
exit 0 binding `patch a251811056b6100759aab75b4863154ba3d3ad3f`, verify exit 0.

**The kind is part of the signed bytes.** The receipt carries
`identities: <n>` followed by `identity: <kind> <value>` lines, kind in
`{change, patch}`, deduplicated and sorted ascending on the whole
`"<kind> <value>"` string. A `patch` identity therefore **never** satisfies a
`change` identity, and the same value under a different kind is its own failure:

```
FAIL — identity KIND mismatch: value(s) <vals> are attested under a different identity kind than the commit(s) under test resolve to; a patch identity never satisfies a change identity
```

That is deliberate, not an oversight — interchangeable kinds would be a forgery
surface. Selftest cases (d5), (d6) and (d7) pin the cross-kind and same-value
rejections; (d3) pins that a patch-id identity signs and verifies with no
change-id header; (d4) pins that a merge commit is unbindable. The workflow-side
`decide()` additionally refuses a PR that **mixes** kinds within one range
(`the PR mixes <a> and <b> commit identities; comparing unlike identities is a
forgery surface`).

What is still genuinely unbindable, and lands in `full`: **merge commits** with
no change-id header (patch-id is undefined for a merge — rebase instead of
merging), and commits with an **empty diff** and no header. Check your own
commits when a verdict surprises you:

```bash
for c in $(git rev-list <base>..HEAD); do
    printf '%s ' "$c"
    git cat-file commit "$c" | awk '$1=="change-id"{print $2; found=1; exit} /^$/{exit} END{if(!found) print "NO-CHANGE-ID"}'
done
```

A `NO-CHANGE-ID` line is **fine** — that commit binds as `patch` instead, as long
as it is not a merge and its diff is non-empty. Whether your local jj writes the
header depends on jj configuration; verify with the loop above rather than
assuming. What you must avoid is a range that mixes the two kinds.

---

## 9. What to do when it says `full`

`full` is the correct, safe answer to every uncertainty. It is not an error to
suppress. Read the `reason` in the `LOCAL-CI-RECEIPT MODE:` line and match it:

| reason (substring) | what it means | what to do |
|---|---|---|
| `event "<x>" is not a pull request` | push or dispatch run | nothing; receipts apply to PRs only |
| `the BASE ref carries no verify-local-ci-receipt.shs` / `no ci_receipt_allowed_signers` / `no gate manifest` | your base predates the feature | rebase onto a base that has it |
| `ssh-keygen is absent on this runner` | runner precondition | nothing you can do from the PR |
| `could not fetch the PR endpoints (git exit <n>)` | shallow-checkout fetch failed | re-run the job |
| `range holds <n> commit(s) but the PR payload declares <m>` | shallow or rewritten history | push once more so the payload and the range agree; avoid repeated force-pushes |
| `the PR range is empty; there is nothing to attest` | no commits | nothing to do |
| `the PR edits check policy (<path>)` | you touched `.github/workflows/`, `scripts/check/`, `scripts/hooks/` or `config/check/` | expected and non-negotiable — split policy edits into their own PR (§5) |
| `commit <sha> is a merge commit with no change-id header` | patch-id is undefined for a merge, so it is unbindable | rebase instead of merging |
| `has neither a jj change-id header nor a stable patch-id: unbindable` | a merge, or a commit with an empty diff | drop the empty commit; rebase away the merge |
| `the PR mixes <a> and <b> commit identities` | some commits bind as `change`, some as `patch` | make the whole range one kind |
| `no refs/notes/ci-receipts on origin: this PR carries no receipt` | the notes ref has never been pushed | §7 — attach and push the note |
| `no ci-receipt note on head <sha>` | no note keyed to **this** head; usually a rebase or amend after publishing | re-sign and re-attach to the new head sha (§7) |
| `the ci-receipt note on <sha> carries no payload` / `carries no sshsig block` | the note body is not `payload \|\| signature` | rebuild it with `cat receipt sig > /tmp/note` (§7) |
| `receipt not admitted (verifier exit <n>): <verdict>` | the verifier decided — its verdict is quoted inline | look the verdict up in §10 |
| `the BASE manifest declares no ci row for job code-idiom-gates` | manifest has no `ci` rows for this job at your base | rebase |
| `receipt verified but the merge diff could not be computed` / `could not assemble the changed-path set` | `escalate` could not bound itself, so it fell back | re-run the job |

Meanwhile: **push once.** Every force-push cancels the in-flight run and re-queues
you behind everything else (§1). Get the message and the rebase right before the
first push.

---

## 10. Troubleshooting, keyed on the verifier's actual verdict strings

The verdict line is **always the last line of stdout**, in exactly one of three
shapes:

```
PASS — <n> row(s) verified, receipt binds tree <sha> (signer <id>)      exit 0
FAIL — <reason naming the offending row/field>                          exit 1
ERROR — nothing was checked (<reason>)                                  exit 2
```

Non-vacuity is absolute: 0 rows verified is `ERROR`, never `PASS`. The signer's
PASS line is the parallel `PASS — <n> row(s) signed, receipt binds tree <sha>
(signer <id>)`.

### `ERROR — nothing was checked (…)` — the verifier could not decide

| reason | fix |
|---|---|
| `git is not on PATH` | install git |
| `ssh-keygen is not installed; a receipt cannot be verified` | install OpenSSH |
| `cannot parse an OpenSSH version out of \`ssh -V\`` | non-standard ssh build; use a stock OpenSSH |
| `OpenSSH is older than 8.0; sshsig (ssh-keygen -Y) is unavailable` | upgrade to ≥ 8.0 |
| `cannot locate the repository root` / `cannot canonicalize the repository root` | run from inside the repo, or pass `--root` |
| `receipt <p> does not exist` | you have not minted one, or `--receipt` points elsewhere — §7 |
| `receipt <p> is a symlink` / `signature <p> is a symlink` / `allowed-signers file <p> is a symlink` | symlinks are rejected on every loaded path by design; use real files |
| `receipt <p> is empty` / `signature <p> is empty` | re-run the signer |
| `signature <p> does not exist` | the signer writes `<out>.sig`; keep it beside the receipt |
| `allowed-signers file <p> does not exist` | §5 |
| `cannot resolve <rev>^{tree} in <root>` | bad `--rev` |
| `tree <sha> has no config/check/must_check_gates.sdn` | the tree predates the manifest |
| `revision spec "<spec>" selects no commit` / `cannot enumerate commits for "<spec>"` | bad `--changes` |
| `no identity could be resolved for "<spec>"` | §8 |
| `config/check/must_check_gates.sdn at tree <t> declares no row in tier "<tier>"` | wrong `--tier`, or a tree without `ci` rows |
| `0 row(s) were verified` | vacuous receipt; re-mint |
| `the mandatory verifier selftest failed; no receipt was examined` | the verifier is broken on this host — do **not** treat as a pass; report it |

### `FAIL — …` — the verifier decided against the receipt

| reason | what actually happened |
|---|---|
| `receipt <p> is not canonical: <why>` | the payload is not the fixed field order / sorted set the signer emits. Re-mint; do not hand-edit a receipt |
| `signature <p> does not cover the bytes of <p> (payload tampered, wrong namespace, or malformed signature)` | the payload changed after signing, or the signature was made under a different sshsig namespace. Note `ssh-keygen -Y verify` exits **255** on tamper, not 1 |
| `signer identity "<id>" is not an allowed signer for namespace simple-ci-receipt in <p> (or its key does not match the signature)` | key not in the allowlist, missing `namespaces="simple-ci-receipt"`, or `--identity` ≠ the principal line. §5 |
| `commit(s) resolve to no rebase-stable identity and are therefore unbindable (no jj change-id header, and no patch-id — a merge commit or an empty diff): <shas>` | a merge, or an empty-diff commit. §8 |
| `field identities: receipt declares <n> identity(ies) but carries <m>` | corrupt payload; re-mint |
| `identity KIND mismatch: value(s) <vals> are attested under a different identity kind than the commit(s) under test resolve to; a patch identity never satisfies a change identity` | you signed under one kind and CI resolved the other. Re-sign against the actual PR range. §8 |
| `identity set differs from the receipt (attested <n>, tested <m>); this is different work, not a rebase` | you signed a different commit set. Re-sign with the `--changes` range that matches the PR |
| `identities match but tree differs (attested <a>, tested <b>); rebased since signing` | **the rebase case** — same work, new bytes. This is what `escalate` exists for; re-sign and re-attach the note after the rebase to get back to `sanity` |
| `field manifest_sha: receipt binds <a> but config/check/must_check_gates.sdn at tree <t> is blob <b>` | the manifest moved under you; rebase and re-sign |
| `field tier: receipt covers tier "<a>" but tier "<b>" was requested` | you signed with the default `--tier push`. Re-sign with `--tier ci` |
| `manifest row id "<id>" is declared twice` | manifest defect; fix the manifest |
| `field rows: receipt declares <n> row(s) but carries <m>` | corrupt payload; re-mint |
| `receipt omits manifest row(s) in tier "<t>": <ids>` | your results file is missing rows. The id set must **equal** the manifest's |
| `receipt carries row(s) absent from the manifest in tier "<t>": <ids>` | stale results file after a manifest change; rebase and re-run |
| `row(s) not pass: <ids>` | the gates genuinely failed. Fix the code — this is the feature working |

Every one of these means CI runs the full gate set. **A verifier that cannot
decide is a FAILURE, never a pass. Absence of evidence is never evidence.**

---

## 11. Known limits and future work

- **Publishing the note is manual** (§7): `sign-local-ci-receipt.shs` has no
  `--note` flag. This is the top usability gap and the first thing to close.
- **Never exercised on a CI runner.** Every result in this guide is local. The
  runner-side path — notes fetch, base-policy materialization, the mode
  decision — has no observed green run yet.
- **`escalate` degrades to `full`** when the attested tree cannot be materialized
  on the runner. An optional non-identity `attested_commit` fetch hint would fix
  it; it is not built.
- **Coverage honesty.** The idiom job runs 27 guard scripts and they do not share
  a verdict grammar (`check-cpu-hotloop-idiom.shs` prints
  `cpu_lane_hotloop_ok=true`, not a `PASS —` line), so receipt rows key on **exit
  status**, not on parsed output.
- **The conflict-class guards are blocking in every mode**, including `full`.
  They have not yet run in a CI context, so if one turns out to be wrong about
  CI-shaped ranges it will redden PRs; that risk was accepted deliberately over
  an advisory tier, because in `sanity` and `docs` they are the only enforcement
  left.
- **A pure-Simple twin verifier** over `src/lib/common/crypto/ed25519.spl` is the
  recorded upgrade path, so the check stops depending on OpenSSH being on the
  runner. It is blocked on a full-CLI pure-Simple binary being deployed to CI —
  CI runners have no `bin/simple` today. Do not build it before then.

---

## Related

- `.claude/skills/spipe.md` § *Landing a PR here* — the surrounding PR-landing
  mechanics (single push, admission traps, ruleset behaviour).
- `.claude/rules/vcs.md` — the push-tier guard manifest and what actually
  enforces on push, which is a different surface from this one.
- `doc/00_llm_process/feature_expert/must_check_tiering/skill.md` — the
  manifest/ledger feature knowledge this receipt extends.
