# Local CI receipt — operator guide

**Audience:** a developer who wants their PR's required
`Code Idiom & Structural Ratchet Gates` context to take a fast path instead of
re-running 27 gate scripts on a saturated runner queue.

**Status, measured 2026-09-06 against `origin/main` `4699194f81e`:** the signer,
the verifier, the allowed-signers trust root and the three-mode decision in
`repo-hygiene.yml` have all landed. **No real PR in this repo can reach `sanity`
or `escalate` today.** Two independent gaps block it — receipt delivery
(§7) and commit identity (§8). Both are stated here rather than hidden, because
a guide that promises a fast path you cannot reach is worse than no guide. Read
§7 and §8 before you spend time generating a key.

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
- the change-id set and the tree binding
- the manifest binding and the manifest↔receipt id-set cross-check
- the per-row status
- the conflict-class guards (conflict-tree, conflict-markers, tree-size) — these
  run in every mode **in which the PR range resolved** (their step carries
  `if: steps.receipt.outputs.range != ''`, so a `full` decision that returned
  before the range was computed skips them too; the workflow's own comment
  overstates this as "every mode"). They matter because a receipt attests the tree
  the developer ran gates on while CI tests the **merge** of that head against a
  base that moves every few minutes. `main` was wiped to four files twice in 24 h
  with every other check green.

---

## 3. The three modes

There is no binary skip. The decision is three-way, made by the
`Local CI receipt admission` step of `code-idiom-gates`, and it only ever
*widens* trust — every failure path returns with the mode still `full`.

| mode | condition | what runs | budget |
|---|---|---|---|
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
pre-push signal available. Pass the **same** `--rev` and `--changes` CI will:

```
sh <base>/scripts/check/verify-local-ci-receipt.shs --root "$PWD" --rev "$HEAD_SHA" \
    --changes "$BASE_SHA..$HEAD_SHA" --tier ci \
    --receipt doc/08_tracking/check/local_ci_receipt.v1.txt --allowed-signers "$signers"
```

Note the default `--tier` differs between the two scripts: the signer defaults to
`push`, the verifier defaults to the receipt's own `tier` field, and CI demands
`ci`. **Always pass `--tier ci` when signing for CI.**

---

## 7. Where the receipt goes — and the delivery gap

As landed, `repo-hygiene.yml` reads the receipt as the tracked path
`doc/08_tracking/check/local_ci_receipt.v1.txt` (plus `.sig`) out of the PR head
checkout. That means the receipt must be **committed into the tree it attests**,
and there is no fixed point: writing the receipt changes the tree, which changes
the `tree` field the receipt binds, which invalidates the signature. The design
identified this exact circularity (`design.md` §3.1, §6.2) and chose a different
home:

> **D2.** Receipt lives in a **git note under `refs/notes/ci-receipts`, keyed by
> the TREE object**, not by a commit.

**That is not implemented.** `git notes` and `ci-receipts` appear zero times in
`sign-local-ci-receipt.shs`, `verify-local-ci-receipt.shs` and
`repo-hygiene.yml`, and `doc/08_tracking/check/` contains no receipt file. Until
the note-based delivery lands, minting and verifying a receipt works end to end
**locally**, and the CI consumer cannot find one, so every PR lands in `full`.

Do not try to route around this by committing the receipt and re-signing: each
commit or amend moves the tree again, and adding a commit to the range also
changes the `--changes` set the verifier compares. `design.md` §6.2 also rejects
workflow artifacts (attacker-controlled, produced by CI rather than by the
developer), PR comments (mutable, and Markdown mangles the exact bytes
`design.md` §4 depends on) and commit trailers.

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

### The commit-identity gap — why *your* PR says `full` today

Before verifying anything, `decide()` resolves a rebase-stable identity for every
commit in `BASE..HEAD`, fail-closed at each step:

1. **jj `change-id` header.** jj writes `change-id <id>` into the git commit
   object header, so plain `git cat-file commit <sha>` reads it and no jj binary
   is needed. It survives rebase, amend and force-push.
2. **`git patch-id --stable`**, for commits that carry no such header. It hashes
   the diff, so like a change-id it survives rebase and cherry-pick — and unlike
   one it is **undefined for a merge commit**, which is therefore unbindable.
3. Neither ⇒ unbindable ⇒ `full`.

The two kinds are never mixed in one set; a PR carrying both is refused
(`the PR mixes <a> and <b> commit identities; comparing unlike identities is a
forgery surface`).

**Measured 2026-09-06: 0 of the last 40 `origin/main` commits and 0 of PR #380's
head commits carry a change-id header.** Commits reaching GitHub are either
GitHub merge commits or plain-git commits produced by this repo's documented
`git worktree add --detach` + `gh pr create` landing route, and neither writes
one. So today's real PRs resolve as `patch-id`.

**And `verify-local-ci-receipt.shs` reads change-id headers only.** It has no
patch-id path and deliberately no fallback identity — inventing one would make an
unbindable commit look bound. A PR whose identity resolved as `patch-id` is
therefore refused by the verifier with

```
FAIL — commit(s) carry no jj change-id header and are therefore unbindable: <shas>
```

and lands in `full`. `repo-hygiene.yml` carries this as an explicit NOTE at the
same spot. It is fail-closed and correct, and it is also **every real PR in this
repo today**. Closing it needs a patch-id identity kind in the receipt schema,
owned by the signer/verifier lane.

Check your own commits before assuming anything:

```bash
for c in $(git rev-list <base>..HEAD); do
    printf '%s ' "$c"
    git cat-file commit "$c" | awk '$1=="change-id"{print $2; found=1; exit} /^$/{exit} END{if(!found) print "NO-CHANGE-ID"}'
done
```

Any `NO-CHANGE-ID` line means `full`, regardless of your key, your receipt or
your gate results. Whether your local jj writes the header depends on jj
configuration; verify with the loop above rather than assuming.

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
| `commit <sha> is a merge commit with no change-id header` | merges are unbindable by patch-id | rebase instead of merging |
| `has neither a jj change-id header nor a stable patch-id: unbindable` | identity gap, §8 | see §8 |
| `the PR mixes <a> and <b> commit identities` | mixed change-id and patch-id commits | make the whole range one kind |
| `receipt not admitted (verifier exit <n>): <verdict>` | the verifier decided — its verdict is quoted inline | look the verdict up in §10 |
| `the BASE manifest declares no ci row for job code-idiom-gates` | manifest has no `ci` rows for this job at your base | rebase |

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
| `no change-id could be read for "<spec>"` | §8 |
| `config/check/must_check_gates.sdn at tree <t> declares no row in tier "<tier>"` | wrong `--tier`, or a tree without `ci` rows |
| `0 row(s) were verified` | vacuous receipt; re-mint |
| `the mandatory verifier selftest failed; no receipt was examined` | the verifier is broken on this host — do **not** treat as a pass; report it |

### `FAIL — …` — the verifier decided against the receipt

| reason | what actually happened |
|---|---|
| `receipt <p> is not canonical: <why>` | the payload is not the fixed field order / sorted set the signer emits. Re-mint; do not hand-edit a receipt |
| `signature <p> does not cover the bytes of <p> (payload tampered, wrong namespace, or malformed signature)` | the payload changed after signing, or the signature was made under a different sshsig namespace. Note `ssh-keygen -Y verify` exits **255** on tamper, not 1 |
| `signer identity "<id>" is not an allowed signer for namespace simple-ci-receipt in <p> (or its key does not match the signature)` | key not in the allowlist, missing `namespaces="simple-ci-receipt"`, or `--identity` ≠ the principal line. §5 |
| `commit(s) carry no jj change-id header and are therefore unbindable: <shas>` | **the common one today.** §8 |
| `field change_ids: receipt declares <n> change(s) but carries <m>` | corrupt payload; re-mint |
| `change-id set differs from the receipt (attested <n>, tested <m>); this is different work, not a rebase` | you signed a different commit set. Re-sign with the `--changes` range that matches the PR |
| `change-ids match but tree differs (attested <a>, tested <b>); rebased since signing` | **the rebase case** — same work, new bytes. This is what `escalate` exists for; re-sign after the rebase to get back to `sanity` |
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

- **Delivery is unimplemented** (§7). This is the first thing to close.
- **Patch-id identity is not in the receipt schema** (§8). This is the second.
- **`escalate` degrades to `full`** when the attested tree cannot be materialized
  on the runner. An optional non-identity `attested_commit` fetch hint would fix
  it; it is not built.
- **Coverage honesty.** The idiom job runs 27 guard scripts and they do not share
  a verdict grammar (`check-cpu-hotloop-idiom.shs` prints
  `cpu_lane_hotloop_ok=true`, not a `PASS —` line), so receipt rows key on **exit
  status**, not on parsed output.
- **The conflict-class guards are advisory in `full` mode only.** They record
  their verdict rather than failing the job there, because they have never run in
  a CI context before and a brand-new blocking gate that is wrong about CI-shaped
  ranges would redden every PR. In `sanity` and `escalate` they are blocking, and
  they are the only enforcement left. Promote them to blocking in all modes once
  a run of each has been observed green in CI.
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
