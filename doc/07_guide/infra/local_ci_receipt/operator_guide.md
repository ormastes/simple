# Local CI receipt — operator guide

**Audience:** a developer who wants the `code-idiom-gates` extended job (and,
via a separate `local`-tier receipt, the push hook) to skip re-running gate
scripts it has already seen pass locally.

**Status, updated 2026-09-24.** **`code-idiom-gates` is no longer the required
status context.** Since 2026-09-23 the ruleset's required check is `fast-gates`
(context `Code Idiom & Structural Ratchet Gates`) in `repo-hygiene.yml`, which
a `ci`-tier receipt never skips. `code-idiom-gates.yml` (the extended,
non-required job this receipt targets) was split out of `repo-hygiene.yml` the
next day into two workflows — see §1a. Today, signing a `ci`-tier receipt
reduces work on that non-required extended job and, transitively, shortens the
window in which it can queue-starve; it does not itself satisfy the ruleset.
Verified end to end locally on `c70a818a0`, a commit with **no** change-id
header: sign exit 0 binding `patch a251811056b6100759aab75b4863154ba3d3ad3f`,
verify exit 0, tamper exit 1. Current local selftests (2026-09-23): verifier
25/25, signer 33/33, including note attach, push, exact-byte round trip, and
rejected-push handling.

Three things you must know before relying on it:

1. **Delivery is explicit but automated.** The signer supports `--note` and
   `--push-note`; publishing a note is opt-in and occurs only after a successful
   local verdict. See §7.
2. **`config/check/ci_receipt_allowed_signers` carries exactly one enrolled
   key today** (`ormastes@simple-ci-receipt`), and shipped with zero as its
   fail-closed default before that. Nothing is admitted for an identity not
   listed there — §5.
3. **A local PASS is not a GitHub required-check PASS**, and (since the
   2026-09-23 ruleset change) `code-idiom-gates` is not even the required
   check. The gate job must import and re-validate the base decision against
   the PR head it actually checked out; do not merge on local output alone.

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

("Unreachable" above describes **`code-idiom-gates` as it ran under
`repo-hygiene.yml` before 2026-09-23, when it was still the required check
without a receipt.** It is not a statement about the receipt fast path, which
works locally; see the Status block.)

### 1a. 2026-09-23/24: the required check moved, and the job split in two

`repo-hygiene.yml` now carries a separate `fast-gates` job (context
`Code Idiom & Structural Ratchet Gates`) that is the ruleset's actual required
check; it is a fixed, short set of gates and is **not** what this receipt
skips. The former `code-idiom-gates` job — the one this whole document is
about — moved to its own file, `.github/workflows/code-idiom-gates.yml`, kept
its job id (so the manifest's `ci_job=code-idiom-gates` rows still key on it)
but is no longer required, and is now split into two workflows:

- `.github/workflows/code-idiom-receipt.yml` — `pull_request_target` (types
  `opened`/`synchronize`/`reopened`, PRs into `main` only), **no checkout, no
  head script**. It fetches the head only as blobless git objects into a
  private repo under `RUNNER_TEMP`, reads the verifier, the allowed-signers
  file and the manifest with `git show <BASE_SHA>:<path>` (no working-tree
  checkout of the base either), decides `mode`/`skip_ids`/`tree`/`docs_only`,
  and uploads that decision as artifact `receipt-decision-<head sha>`.
- `.github/workflows/code-idiom-gates.yml` — `pull_request`, runs the actual
  gate scripts against the PR head with only the PR's own Actions cache scope,
  and **imports** the base decision (never decides it) — it accepts an
  artifact only from a run the API reports as
  `event=pull_request_target`, `path=.github/workflows/code-idiom-receipt.yml`,
  `completed`/`success`, whose pr/head/base fields match its own payload and
  whose `tree` equals what it actually checked out. Anything else is `full`.

This closes the design gap recorded in Addendum A below (landed in PR #1467).
The reason for two workflows rather than one `pull_request_target` job running
the gates directly: a `pull_request_target` job runs in `main`'s Actions cache
scope, so head code executing there could poison caches that `release.yml` /
`cache-main-writer.yml` restore ("Cacheract"). Splitting the decision (no head
execution) from the gates (head execution, but only in the PR's own cache
scope) removes that path. Honest limit, unchanged by the split:
`code-idiom-gates.yml` is still a `pull_request` workflow, so its own YAML is
still the PR head's — a PR editing that file can still drop its own gates.
What the split fixes is narrower: the skip *authority* can no longer be
produced or widened by head content.

PR #1473 (same day) reworked the gates job's decision-import polling from a
fixed ~5 s loop to a cheap-first backoff (10→20→30 s, capped) that checks a
1-call "how many decision runs exist / how many are pending" probe before ever
listing or downloading artifacts, and remembers runs it has proven invalid so
they are not re-fetched — see §1b for why this mattered in practice on
2026-09-24.

---

### 1b. 2026-09-24: signing needs an enrolled key on the signing host, and it does not buy queue time

Two facts measured the same day, both worth internalizing before relying on
this feature:

1. **Signing needs the enrolled private key present on the host that signs.**
   A Windows development host used on 2026-09-24 had no SSH keys at all and
   could not sign anything; the enrolled key (`ormastes@simple-ci-receipt`)
   lives on a different machine. There is no way around this: `ssh-keygen -Y
   sign` needs the private key file, full stop. To give a new host a signing
   identity: generate a **distinct** ed25519 key for that host (never reuse a
   key already enrolled elsewhere or used for anything else —
   `ssh-keygen -t ed25519 -C ci-receipt-<host> -f ~/.ssh/simple_ci_receipt`,
   e.g. principal `ormastes-win@simple-ci-receipt` for a Windows host), then
   land its public half in `config/check/ci_receipt_allowed_signers` through
   its own reviewed PR (§5). A distinct identity per host means a compromised
   or retired host's key can be revoked on its own line, without touching any
   other host's trust. **Adding a signer is a trust decision** — the reviewer
   is deciding to let that host's local runs stand in for CI's, exactly the
   trust class in §2.
2. **A receipt does not buy queue time.** On 2026-09-24, GitHub Actions for
   this repository was itself saturated: 25 of the last 40 runs sat queued,
   and `code-idiom-receipt.yml` decision runs were observed queued for **~50
   minutes** without starting. The decision run is itself an ordinary CI job —
   when the Actions queue is full, it does not start, `code-idiom-gates.yml`'s
   importer waits out its full `RECEIPT_WAIT_S=300` (5 min) window (see §1a's
   PR #1473 backoff — this is exactly the situation it was tuned for) and then
   falls back to `full`. A receipt reduces the **work** the gates job does
   once a runner is actually available; it does nothing about how long the
   job waits for a runner. If the wait itself is the operational problem
   (rather than the gate work), the tool for that is the kill switch: setting
   the repo variable `SIMPLE_CI_RECEIPT_DISABLED` to anything other than
   `false` forces every decision to `full` immediately, which does not shorten
   queue time either but at least stops the 5-minute import wait on every PR.

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
  because a receipt attests the tree the developer signed hours or days
  earlier, and `main` moves every few minutes; `code-idiom-gates.yml` checks
  out and tests the PR **head sha** directly (not a merge tip — the former
  `escalate` mode compared the attested head against a merge tree and was
  removed on 2026-09-24 once the strict up-to-date ruleset made head and merge
  tree equal at land time), but the range between the receipt's base and that
  head is still exactly what the conflict-class guards re-check. `main` was
  wiped to four files twice in 24 h with every other check green.

---

## 3. The modes

There is no binary skip. The decision is made by the `Local CI receipt
admission` step of `code-idiom-receipt.yml` (base-only; §1a) and *imported*,
never re-decided, by `code-idiom-gates.yml`'s own `Local CI receipt admission
(import base decision)` step. It only ever *widens* trust — every failure path
leaves the mode `full`.

**Updated 2026-09-24: there are three modes, and only three** — `full`,
`docs`, `sanity`. The former `escalate` mode (which compared the attested head
tree against the merge tree the gate job tested) was removed the same day: the
gate job now checks out and tests the PR head sha directly, and the strict
up-to-date ruleset makes head and merge-tip equal at land time, so `escalate`'s
branch could never fire. If you find an older note (including earlier drafts
of this guide) saying "four modes, the header comment is stale," that was true
before 2026-09-24 and is no longer true — the code and the header now agree on
three.

| mode | condition | what runs | budget |
|---|---|---|---|
| `docs` | receipt verifies **and** every changed path is documentation | the conflict-class floor only | ≤ 60 s |
| `sanity` | receipt verifies **and** the attested `tree` equals `HEAD^{tree}` of the tree this job actually checked out | receipt verify + conflict-tree + conflict-markers + tree-size | ≤ 60 s |
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

Use a key that signs **nothing else**, and a **distinct key per host** — see
§1b. Reusing an existing SSH key means a signature you made for some other
purpose is one namespace check away from being replayed as a CI receipt;
reusing one key across hosts means a compromised or retired host cannot be
revoked without also revoking every other host's trust.

```bash
ssh-keygen -t ed25519 -C ci-receipt-<who>-<host> -f ~/.ssh/simple_ci_receipt
```

Requires OpenSSH ≥ 8.0 for `ssh-keygen -Y` (sshsig). Both scripts assert this
and **ERROR** rather than skipping when it is absent or unparseable.

```bash
ssh -V        # OpenSSH_10.3p1 measured locally; runners are well past 8.0
```

---

## 5. Getting your key into `config/check/ci_receipt_allowed_signers`

**The file shipped with ZERO keys, by design, and as of 2026-09-24 carries
exactly one enrolled signer:** `ormastes@simple-ci-receipt` (also the identity
used by the separate `pr`-tier PR fast check, §6). A key not listed here is
not admitted, full stop — the empty-by-default posture is the intended
fail-closed baseline: an allowlist with no key admits nobody, every
verification returns non-zero, and CI therefore runs the full gate set. The
verifier selftest's `c2` case ensures an untrusted fixture signer is not
admitted by the shipped file; a reviewed signer may be enrolled in a separate
PR without weakening that invariant. Adding a signer is a trust decision (§1b)
— give each host its own identity rather than sharing one across hosts.

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

1. The allowed-signers file, the verifier script and the manifest are read
   with `git show <BASE_SHA>:<path>` into a private repo under `RUNNER_TEMP` —
   **not a checkout** of any kind, base or head (§1a: `code-idiom-receipt.yml`
   has no `actions/checkout` step at all). Otherwise a PR could add its own key
   and sign its own receipt.
2. `decide()` refuses admission outright for any PR that touches
   `.github/workflows/`, `scripts/check/`, `scripts/hooks/`, `scripts/lib/`,
   `scripts/setup/` or `config/check/`:

   > `the PR edits check policy (<path>); a receipt may never admit its own rules`

   So **the PR that adds your key always runs `full` itself.** That is correct
   and not a bug to route around. Reviewers should reject a PR that adds a key in
   the same change whose gates that key would let it skip.

---

## 6. Running the local gates and minting a receipt

**There are three separate receipt lanes. Do not conflate them — a receipt
signed for one tier is not accepted for another, and the verifier's own
`field tier: receipt covers tier "<a>" but tier "<b>" was requested` FAILs on
a mismatch.**

| tier | manifest | what it covers | who consumes it |
|---|---|---|---|
| `ci` | `config/check/must_check_gates.sdn`, 27 rows, `ci_job=code-idiom-gates` (still 27 as of 2026-09-24) | the extended, non-required `code-idiom-gates` job's gate steps | `code-idiom-gates.yml`'s importer, via a note on `refs/notes/ci-receipts` |
| `local` | same file, 6 rows (`local-sdn-crc32-sealed`, `local-rust-duplicate-reexport`, `local-no-stale-snapshot-rewind`, `local-range-shs-hygiene`, `local-rt-dual-implementation`, `local-linux-phase2-test-runner-contract`), all `ci_job=fast-gates` (2026-09-24, WP3 — was `-`) | the gates the 10 s push hook demoted on 2026-09-24 for being too slow for that budget (22-53 s each on Windows) | `scripts/check/run-gate-tier.shs --tier local ...` runs them (plus the push tier's own 4 push_blocking=true rows, unioned in — see that script's header) both locally, fed to `sign-local-ci-receipt.shs --results`, and remotely as `.github/workflows/repo-hygiene.yml`'s required `fast-gates` job. `code-idiom-gates.yml` still re-runs the equivalent checks itself as its own "Push-tier core gates" step. **Do not `--note`/`--push-note` a `local`-tier receipt expecting it to skip anything in the `ci`-tier verifier** — that call is always `--tier ci`, and a `local`-tier note would simply FAIL the tier check |
| `pr` | same file, 1 row (`pr-fast-changed`) — folded in from the former standalone `config/check/pr_fast_gates.sdn` on 2026-09-24, WP3 | the non-required `<1 min PR fast check` (changed-file compile + unit/feature specs) | `pr-fast-check.yml`, via a note on `refs/notes/pr-fast-receipts`; §12 |

This section covers the `ci` lane. The manifest columns are:

```
must_check_gates |id, tier, push_blocking, mode, command, ci_job, inputs, description|
```

`ci_job` maps a row to the CI job that may skip it. `inputs` is retained by the
schema for a future bounded-diff mode; today no mode reads it (the `escalate`
mode that once intersected it against the rebase diff was removed 2026-09-24,
§3), so `inputs` is inert for every currently emitted mode.

**Cost, so you know what you are signing up for before running `--tier ci
--run`:** several rows are slow even outside CI — the manifest's own
`orphaned-docstring-tail` row measures ~65 s over the tree, several rows need a
deployed full-CLI `bin/simple` (6b covers the workaround), and `--tier local`
is no lighter (22-53 s per row on Windows, per the `local` row descriptions
above). Signing either tier for real is a multi-minute local operation, not a
quick pre-push step.

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

## 7. Where the receipt goes — publish it as a git note

CI reads the receipt from **a git note on `refs/notes/ci-receipts`, keyed by the
PR head sha**. It cannot be a tracked file: the receipt binds `tree`, so
committing it into that tree changes the tree, and the bound tree could never
equal the tested one. A note lives outside the commit tree, so attaching one
perturbs nothing.

After the reviewed signer key has landed on the **base** branch and all `ci`
rows have genuinely passed, the signer can attach and publish the exact bytes:

```bash
sh scripts/check/sign-local-ci-receipt.shs \
    --key <dedicated-private-key> --identity <enrolled-principal> \
    --tier ci --run --rev <pr-head-sha> --changes <base-sha>..<pr-head-sha> \
    --allowed-signers config/check/ci_receipt_allowed_signers \
    --out <untracked-receipt-path> --note --push-note --note-remote origin
```

`--note` alone writes only the local notes ref; `--push-note` is the explicit
remote mutation. Use `--results` instead of `--run` only for results from gates
actually executed. A non-PASS receipt is never attached. If a concurrent note
push makes the notes ref non-fast-forward, follow the signer's fetch/merge
recovery message; do not force-push the shared notes ref. The `<pr-head-sha>`
must be the current PR head, never the merge tip.

Notes on the mechanics:

- The note body is the concatenation `payload || signature`. CI splits it back
  apart on the **first line exactly equal to** `-----BEGIN SSH SIGNATURE-----`:
  everything strictly before is the payload, everything from that line on is the
  signature. The signer preserves the exact signed bytes; do not reformat it.
- The note is author-writable, and that is fine. The sshsig signature inside it,
  checked against the **BASE** allowed-signers file, is what protects the
  contents.
- **A missing note is the ordinary case, not an error.** It means the PR carries
  no receipt, which means `full`. You will see
  `no refs/notes/ci-receipts on origin: this PR carries no receipt` or
  `no ci-receipt note on head <sha>`.
- Re-run the gates, re-sign, and publish a new note after **every** rebase or
  amend: the head sha changes, so the old note no longer keys to anything CI
  looks up. The old note is inert, not a substitute for a current receipt.

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
| `base decision attests tree <a> but this job tests <b>` | rebased or amended after signing — same reason as the `identities match but tree differs` verifier verdict below | re-sign and re-attach the note after the rebase (§10) |

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
| `identities match but tree differs (attested <a>, tested <b>); rebased since signing` | **the rebase case** — same work, new bytes. There is no partial-credit mode for this any more (`escalate` was removed 2026-09-24); re-sign and re-attach the note after the rebase to get back to `sanity` |
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

- **`code-idiom-gates` is not the required check** (§1a, since 2026-09-23).
  This whole receipt lane reduces work on a non-required job; it does not by
  itself satisfy the branch-protection ruleset (`fast-gates` does, and this
  receipt does not touch it).
- **Publication is opt-in** (§7): `--note` attaches locally, while
  `--push-note` publishes to the shared notes ref. The operator must still
  select a trusted key and run all claimed gates before publishing.
- **Exercised on a CI runner as of the 2026-09-24 split (PR #1467), but not
  load-tested.** The decision/import mechanism has run for real PRs since the
  split; what remains unverified is its behavior under the queue saturation
  described in §1b beyond "it correctly falls back to `full`."
- **`code-idiom-gates.yml`'s own YAML is still the PR head's** (§1a): a PR that
  edits that file can drop its own gates, with or without a receipt. The split
  narrows what a receipt can forge; it does not make the gates job itself
  immune to a head edit, which is inherent to every `pull_request` workflow in
  this repo.
- **The `pr`-tier PR fast check's `session_id` field carries binary identity**
  (the simple binary's size + sha256) as a documented v1 shape (§12) — this is
  a deliberate, not accidental, coupling between a receipt and the exact binary
  that produced its verdicts.
- **Coverage honesty.** The idiom job runs 27 guard scripts and they do not share
  a verdict grammar (`check-cpu-hotloop-idiom.shs` prints
  `cpu_lane_hotloop_ok=true`, not a `PASS —` line), so receipt rows key on **exit
  status**, not on parsed output.
- **The conflict-class guards are blocking in every mode**, including `full`.
  In `sanity` and `docs` they are the only enforcement left, which was accepted
  deliberately over an advisory tier.
- **A pure-Simple twin verifier** over `src/lib/common/crypto/ed25519.spl` is the
  recorded upgrade path, so the check stops depending on OpenSSH being on the
  runner. It is blocked on a full-CLI pure-Simple binary being deployed to CI —
  CI runners have no `bin/simple` today. Do not build it before then.

---

## 12. The `pr` tier — the PR fast check

A second, independent receipt lane exists alongside the `ci`/`local` tiers
above: `.github/workflows/pr-fast-check.yml` runs
`scripts/check/check-pr-fast.shs`, which compiles changed `.spl` files
(syntax-only by default) and runs their mapped unit and feature specs inside a
60 s budget. It reads its `pr`-tier row (`pr-fast-changed`) out of the same
`config/check/must_check_gates.sdn` as the `ci`/`local` tiers above — folded
in from the former standalone `config/check/pr_fast_gates.sdn` on 2026-09-24
(WP3) — via `RECEIPT_MANIFEST_REL` in `check-pr-fast.shs`, which is now the
same default `sign-local-ci-receipt.shs` / `verify-local-ci-receipt.shs`
already use.

```bash
sh scripts/check/check-pr-fast.shs \
    --sign-key ~/.ssh/simple_ci_receipt --sign-identity <principal> \
    --publish origin
```

This signs a `pr`-tier receipt over the exact head tree and change set and
publishes it on `refs/notes/pr-fast-receipts` (a **different** notes ref from
the `ci` tier's `refs/notes/ci-receipts`). `pr-fast-check.yml` runs the same
script in `--verify-receipt` mode, follows the same base-only trust model as
`code-idiom-receipt.yml` (`pull_request_target`, the script/verifier/allowed-
signers file read from BASE via `git show`, no head execution), and is
**not** a required check today — not because of signer enrollment (the same
`ormastes@simple-ci-receipt` key already verifies here) but because the
underlying check itself has rough edges: a PR touching no `.spl` file ERRORs,
a changed file with no mapped spec FAILs outright rather than as a ratchet,
and the 60 s budget does not scale with change-set size. The signed
`session_id` field additionally binds the exact simple binary that produced
the verdicts (its size and sha256) — a documented v1 design choice, not an
oversight, so a receipt can be tied to the toolchain that generated it.

---

## Related

- `.claude/skills/spipe.md` § *Landing a PR here* — the surrounding PR-landing
  mechanics (single push, admission traps, ruleset behaviour).
- `.claude/rules/vcs.md` — the push-tier guard manifest and what actually
  enforces on push, which is a different surface from this one.
- `doc/00_llm_process/feature_expert/must_check_tiering/skill.md` — the
  manifest/ledger feature knowledge this receipt extends.
