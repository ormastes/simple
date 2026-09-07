# Local CI receipt + signing — research

Measured 2026-09-06 against `origin/main` `4699194f81e34f4dad7af088e9b8d24c375c5568`,
from an isolated detached worktree. Every number below names the command or
`file:line` that produced it. Where a claim is an extrapolation, it says so.

The binding facts and design decisions this builds on are in the session brief
(F1-F10): only two checks are required to merge, `Code Idiom & Structural Ratchet
Gates` is the primary target, the receipt half-exists in
`config/check/must_check_gates.sdn` + `doc/08_tracking/check/must_check_db.sdn`,
sshsig is the v1 signing mechanism, config is read from BASE only, and the trust
class is dev-key attestation rather than independent verification. This document
does not re-argue those; it records what the tree actually contains and what that
implies for a v4 schema.

---

## 1. The current CI surface

`.github/workflows/` holds 41 `.yml` files (`ls .github/workflows/ | wc -l` = 41;
no `.yaml`). The two contexts the `spipe-vcs-v3-main` ruleset requires come from
two of them:

| required context | file:line | job id |
|---|---|---|
| `Code Idiom & Structural Ratchet Gates` | `.github/workflows/repo-hygiene.yml:37` | `code-idiom-gates` |
| `SPipe Self Review Admission` | `.github/workflows/review-admission.yml:124` | the broker job |

`repo-hygiene.yml` declares three jobs (`repo-hygiene:20`, `code-idiom-gates:36`,
`advisory-gates:462`) across 883 lines. The `code-idiom-gates` job spans lines
36-461 and contains **25 named steps**, of which one is `Install ripgrep` and 24
are gates, invoking **27 distinct guard scripts**
(`sed -n '36,461p' repo-hygiene.yml | grep -oE 'scripts/[a-z0-9/._-]+\.shs' | sort -u | wc -l`
= 27). Every one of them is a text/tree scan: no `bin/simple`, no cargo, no QEMU,
no network. That property — not the job's name — is what makes this job the right
first target for a locally-produced receipt.

**The required gate is 92% queue, 8% work.** The last successful `repo-hygiene.yml`
run is `33716483100`, created `2026-09-03T04:49:59Z`. Its `code-idiom-gates` job
started `05:25:11Z` and completed `05:28:03Z`
(`gh api repos/ormastes/simple/actions/runs/33716483100/jobs`): **172 s of
execution after 2112 s of queueing.** Skipping the job saves 172 s of runner time
and, far more importantly, removes a 35-minute serialization point from the merge
path.

**It is not merely slow; it currently never finishes.** Across the last 60 runs of
that workflow (`gh run list --workflow=repo-hygiene.yml --limit 60`): **0 success,
26 cancelled, 24 still queued, 10 failure**. The last success was 2026-09-03, three
days before this measurement. The mechanism is `repo-hygiene.yml:10-12`:

```yaml
concurrency:
  group: ${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true
```

Main receives **162 commits in 24 h** (`git log --oneline --since=24.hours
origin/main | wc -l`), one every 8.9 minutes on average, and 2983 in 14 days. A run
that waits 35 minutes to start is cancelled by three or four successors before it
gets a runner. The required check is therefore not blocked by its own cost — it is
blocked by contention it cannot win.

**Runner backlog, repo-wide, measured 2026-09-06 ~04:35Z:** 322 queued workflow
runs against 5 in progress
(`gh api "repos/ormastes/simple/actions/runs?status=queued&per_page=1" -q .total_count`
= 322; `status=in_progress` = 5).

**Per-PR check fan-out.** PR #380: 36 checks, 2 completed / 34 queued. PR #394 at
the same instant: 21 checks, 2 completed / 19 queued (the brief recorded 29 for
#394 earlier the same day — the number churns downward as runs are cancelled, so
record the timestamp with any such count). The 2 completed on both are exactly the
two admission contexts; **every other check on both PRs was still queued, including
both required-adjacent hygiene jobs.** Of #380's 34 queued, the duplicated names
(`Cross — Linux aarch64` twice, `Native — Windows x86_64` six times, and so on)
show the same job re-registered by both the `push` and `pull_request` triggers.

**Trigger census** (`sed -n '/^on:/,/^jobs:/p'` per file). 33 of 41 workflows carry
`pull_request`; 30 carry `push`; only one is `pull_request`-only
(`index-validate.yml`, `Validate Index`). Four are `workflow_dispatch`-only —
`candidate.yml` (932 lines), `pr-admission.yml` (670), `live-kms-security.yml`,
`release-convergence-checkpoint.yml`. The heavy lanes by job count and file size
are `release.yml` (1519 lines, 9 jobs), `candidate.yml` (932/1), `repo-hygiene.yml`
(883/3), `pr-admission.yml` (670/1), `baremetal-tests.yml` (536/9),
`containerized-tests.yml` (478/11), `test-isolation.yml` (432/8),
`cross-platform.yml` (428/9). Since almost everything is dual-triggered on `push`
and `pull_request`, the 322-run backlog is not attributable to PRs alone; a receipt
that skips one job does not fix the backlog, it fixes the *merge path*.

**A latent defect in the target job.** `repo-hygiene.yml:48` states "Every gate step
below carries `if: ${{ !cancelled() }}`". It is false for the first four gates: the
CPU hot-loop, UI backend-isolation, TUI standalone-closure and workspace root-guard
steps (`:69`, `:76`, `:83`, `:89`) have no `if:`; the first `if:` in the job
is `:104`, on the guard-wiring gate declared at `:103`. A red CPU hot-loop
gate therefore still hides the next three — the exact masking failure the comment
block at `:48-66` was written to describe. Per-row receipt granularity (F8) makes
each row's verdict individually visible and would surface this class as a side
effect; it does not by itself fix the workflow, and the workflow fix is a
one-character-per-step edit that should land independently.

---

## 2. The existing receipt machinery, end to end

### 2.1 Manifest — `config/check/must_check_gates.sdn` (78 lines)

Header at `:4`: `must_check_gates |id, tier, push_blocking, mode, command, description|`
— six columns. 74 rows: 23 at `tier=push`, 51 at `tier=bootstrap`. Modes observed
are `tree`, `range`, `ref`, `receipt`, `automated`, `todo` **and `external-receipt`**
(rows `:57-77`) — a seventh mode the brief's summary omits, and the one that matters
most here (§5).

**The manifest covers 1 of the 27 idiom-job scripts.** Intersecting the guard-script
sets:

```
comm -12 <(sed -n '36,461p' .github/workflows/repo-hygiene.yml | grep -oE 'scripts/[a-z0-9/._-]+\.shs' | sort -u) \
         <(grep -oE 'scripts/[a-z0-9/._-]+\.shs' config/check/must_check_gates.sdn | sort -u)
=> scripts/check/check-guard-wiring.shs
```

27 idiom scripts, 38 manifest scripts, overlap 1. F8's "one source of truth" is
therefore not a small edit: it means adding **26 manifest rows** for guards that
today exist only as workflow steps.

### 2.2 Ledger — `doc/08_tracking/check/must_check_db.sdn` (59 lines)

Schema `simple.must-check-ledger/v3`; header fields `source_fingerprint` and
`completed_at_utc`; rows `|id, status, passed_at_utc, command, evidence,
evidence_sha256, owner, unblock_condition|`.

At `origin/main` the ledger is **entirely unpromoted**: `source_fingerprint:
"unrecorded"`, `completed_at_utc: "never"`, 51 rows, **51 `todo`, 0 `pass`**
(`grep -c ', todo,'` = 51, `grep -c ', pass,'` = 0). Its id set is exactly the 51
bootstrap-tier manifest ids; the 23 `push`-tier ids appear in the manifest only
(`comm` of the two id sets: 23 manifest-only, 0 ledger-only). So the ledger is
bootstrap-tier by construction, and every PASS-path branch in the validator below
is, today, dead code that has never executed against real content.

### 2.3 Consumer — `scripts/check/check-push-must-pass.shs` (510 lines)

`validate_ledger_text()` (`:139-249`) is one awk pass over manifest + ledger. What
it already enforces, and what a v4 receipt can lean on unchanged:

- manifest rows are selected by `/^[[:space:]]+[a-z0-9][a-z0-9-]*,[[:space:]]*bootstrap,/`
  (`:157`) — **tier-filtered**; `manifest_command[id]=unquote($5)` (`:162`).
- schema must be exactly `simple.must-check-ledger/v3` (`:189`).
- `manifest_count != ledger_count` fails (`:192`); id-set equality both directions
  (`:203`, `:205-206`); per-id `ledger_command[id] != manifest_command[id]`
  byte-match fails (`:206`).
- a `pass` row must carry an ISO-8601 `passed_at_utc`, a non-placeholder evidence
  path, a 64-hex `evidence_sha256`, `unblock_condition == none` (`:210-215`).
- fail-closed default: `if (bad) exit 1`, and the caller treats a non-zero awk
  status as failure (`:229-231`).

Evidence bytes are then resolved and hashed in the shell loop at `:233-247`.

`run_manifest_push_gates()` (`:288-370`) selects `push,`-tier rows and dispatches on
`"$_id:$_mode:$_command"` through a `case` whose default arm is
`*) rm -f "$_push_rows"; return 2 ;;` (`:365`) — fail-closed, as F9 requires.
`run_push_gate()` (`:273-287`) honours `push_blocking` and reads the exit status
into `_gate_rc` on the line after the invocation, with an explicit comment saying
why it is not a pipeline.

### 2.4 Writer — `scripts/check/check-bootstrap-must-pass.shs` (583 lines)

- `write_ledger()` (`:64-81`) emits the whole file: comment, `must_check_ledger:`,
  schema, `source_fingerprint`, `completed_at_utc`, the row header, then rows;
  written to `$LEDGER.tmp.$$` and `mv`'d — atomic replace, no partial state.
- `receipt_field()` (`:91-96`) is the receipt grammar: flat `key=value` lines,
  `grep -c "^${field}="` must be exactly 1, value via `sed -n "s/^${field}=//p"`.
  Duplicate keys are a hard error, which is the property that makes such a file
  safe to sign as a whole.
- `validate_gate_receipt()` (`:128-155`) checks
  `receipt_schema = simple.must-check-gate-receipt/v1`, `gate_id`,
  `final_verdict = PASS`, and **`source_fingerprint` equal to the expected value at
  `:140`**, then binds `artifact_path`/`artifact_sha256` to a HEAD blob via
  `head_blob_metadata()` (`:42-52`, mode must be `100644`/`100755`, sha computed
  from `git show HEAD:<path>`).

**What already works:** a schema-versioned, fingerprint-bound, blob-bound,
duplicate-key-rejecting receipt format with a fail-closed validator, and a
manifest↔ledger cross-check that already does id-set equality and per-id command
byte-matching.

**What is missing for CI consumption**, precisely:

1. No workflow reads any of it — `grep -rln must_check .github/workflows/` is empty
   (F3), and none of the five in-tree manifest consumers (§6) runs on a runner.
2. Nothing binds a receipt to a **git tree**. Everything binds to
   `source_fingerprint` or to `HEAD:` blobs, both of which are computed against the
   local repository, not against a PR head the runner is testing.
3. The ledger is a single whole-file document with one global fingerprint. There is
   no per-row provenance of *which* tree a row passed against, so a partially
   re-run set cannot be represented.
4. No signature anywhere on this path. Authenticity is currently "the file is
   committed", which is exactly what F6 says must not be trusted from a PR head.
5. `source_fingerprint` does not cover `.github/` (§3), so it cannot be the only
   binding for a decision that a workflow makes.

---

## 3. How `source_fingerprint` is computed today

Two byte-identical implementations, deliberately duplicated:

- `check-bootstrap-must-pass.shs:29-36` `fingerprint_head()`
- `check-push-must-pass.shs:84-92` `fingerprint_rev()`

```sh
git ls-tree -r <rev> -- src scripts config test rules.sdl \
    doc/07_guide doc/00_llm_process doc/glossary.md \
  | sed '\|[[:space:]]doc/08_tracking/check/must_check_db.sdn$|d' \
  | sha256sum
```

So it is a sha256 over the *recursive tree listing* (mode, type, blob sha, path) of
**eight roots**, with the ledger's own line removed so the ledger can record its own
fingerprint without self-reference. Cost measured here: 30 revisions fingerprinted
in 7.9 s wall — **~0.26 s per revision**, negligible.

Three properties that constrain a v4 schema:

- **`.github/` is not in the fingerprint.** Neither is `bin/`, `bootstrap/`,
  `examples/`, `tools/`, or the rest of `doc/`. A PR that edits only
  `.github/workflows/repo-hygiene.yml` produces an *unchanged* fingerprint. A
  fingerprint-bound receipt would therefore be reusable across a workflow rewrite.
  This is dispositive: **the CI binding must be `git rev-parse <head>^{tree}` (F5),
  not the fingerprint.** The fingerprint may travel alongside as a
  cross-check against the existing bootstrap machinery, but it cannot be the
  authority.
- **Churn.** Across the last 30 commits of `origin/main` there are 22 distinct root
  trees and 19 distinct fingerprints. Binding to the fingerprint instead of the tree
  would save 3 re-signings in 30 — not worth deviating from F5.
- **The `$?`-after-a-pipeline anti-pattern lives inside this exact function.**
  `check-push-must-pass.shs:88-89` runs `sed … | sha256sum | awk '{print $1}'` and
  then reads `_rc=$?`, which is `awk`'s status, not the pipeline's. A `sed` or
  `sha256sum` failure yields an empty fingerprint with `_rc=0`. It is currently
  masked because `validate_ledger_text` compares the value and would fail on an
  empty string, but a v4 consumer that reuses `fingerprint_rev` must not inherit
  this shape (F9).

### What `must_check_ledger_unbounded_external_evidence_hash_2026-08-22.md` means here

The bug (32 lines, status RESOLVED, `codex/session-01a023a8`) is that the ledger
consumer accepted **absolute evidence paths** and hashed every PASS row's file with
no size or aggregate bound — so a *committed input* (the ledger) could direct the
local hook to read and hash arbitrary local files, unbounded. The fix, visible in
the current source: `MAX_EVIDENCE_BYTES=67108864` (`:15`), `ALLOW_EXTERNAL_EVIDENCE=0`
(`:16`, set to 1 only inside `--self-test` at `:410`/`:442`),
`resolve_evidence_path()` rejecting absolute paths, `..` traversal and symlinks
(`:96-125`), and a running `_evidence_total` checked before each hash (`:236-240`).

The lesson for v4, stated as a rule rather than a story: **a receipt is
attacker-controlled input that names work for the verifier to do.** Every field that
the verifier dereferences — a path, a count, a byte length, a row list — is an
amplification lever. Concretely, the v4 receipt must not contain: an evidence path
the verifier opens (bind to blob shas already in the tree, or to nothing); an
unbounded row count (the row count is checkable against the manifest id-set before
any per-row work); or any field that selects *which* configuration file to read
(that is F6). The one number in the receipt that governs a loop — the row count —
must be validated against the manifest before the loop runs, not used to size it.
The verifier that already exists in this worktree does exactly that: it parses a
fixed 8-line header, reads `rows` as a bounded non-negative integer, and requires a
terminator line so a truncated or extended receipt is a parse failure rather than a
short read (§5.4).

---

## 4. The admission path

### 4.1 `review-admission.yml` (348 lines, 3 jobs)

Triggers (`:3-34`): `workflow_dispatch` with five inputs, `schedule` every 5 min,
`pull_request_target` on `[synchronize, edited, closed, reopened]`,
`repository_dispatch`, and `push` to `main`/`integration/main`/`release/**`.
Repository-default permissions are `contents: read` (`:39-40`); only the protected
`environment: self-review-admission` jobs request `checks: write`.

**Server-side resolution.** The dispatch input is *only* a PR number — its
description says so explicitly (`:7`, "all provider state is resolved server-side").
The job then re-derives everything from the API: actor id via `gh api users/$ACTOR`
compared against `.authorized_dispatcher.id` in `.github/review-admission-broker.json`
(`:192-193`); repository id/node_id/full_name and default branch (`:194-199`);
`head.sha`, `base.sha`, `base.ref`, base repo id, and PR author id, with
`author_id == actor_id` enforced (`:201-211`); the active ruleset resolved by name,
required to be unique and active, and required to contain a
`required_status_checks` rule with `strict_required_status_checks_policy == true`
naming `SPipe Self Review Admission` (`:216-226`); and `$GITHUB_WORKFLOW_REF` pinned
to `…/review-admission.yml@refs/heads/main` (`:185-186`) so the job refuses to run
from any other ref. The checkout is `ref: main`, `fetch-depth: 1`, `persist-credentials: false` (`:135-138`) — **the F6 precedent: config and logic
come from the default branch, never from the PR head.**

**What `self_attestation` actually asserts.** It is a free-text input that must
equal the literal string `PASS:0:0` (`:182`, `test "$SELF_ATTESTATION" = 'PASS:0:0'`),
and its own input description reads "this is not independent authentication"
(`:24`). Downstream it is expanded into a
`spipe-self-review-self-attestation/1` JSON document (`:247`) carrying repo, PR,
head/base/merge-base shas, `diff_sha256`, session id, reviewer identity/model/effort,
and `verdict:"PASS", p0_count:0, p1_count:0`; that document is sha256'd into
`review_evidence_sha256` and folded into a
`spipe-self-review-request/1` evaluation request (`:262-292`) that states its own
trust class in machine-readable fields: `review_evidence_mode:"self_attested"`,
`review_evidence_broker_authenticated:false`, `self_attestation_authorized:true`,
alongside `policy_db_authenticated:true` and
`provider_resolution_authenticated:true`. The evaluation is performed by
`node scripts/release/self-review-policy-evaluator.mjs` against a policy DB supplied
as `secrets.SPIPE_SELF_REVIEW_POLICY_DB` (`:295-297`).

**Why the dispatch loses to a moving base.** After the provider resolution, the job
fetches the real refs and compares (`:236-241`):

```sh
if [[ "$fetched_base_sha" != "$base_sha" ]]; then
  failure_stage='protected base advanced after provider resolution; …'
  exit 1
fi
```

With `strict_required_status_checks_policy == true` the PR must be up to date with
`main`, and `main` advances every 8.9 minutes. The window between "GitHub told us
`base.sha`" and "we fetched `refs/heads/main`" is therefore frequently lost, and the
decision carries a 600-second expiry (`expires_at_unix=$((now_unix + 600))`, `:257`)
on top. Separately, the `invalidate-pr-event` job (`:43-67`) patches every prior
`success` check-run to `action_required` on any `synchronize` — so **each rebase
costs both required contexts, not one.**

**Could a signed receipt carry the same information?** Partly, and the distinction
matters. The admission broker's value is in the facts it resolves *server-side from
the provider* — actor identity, ruleset shape, base advancement, the PR's own
head/base — none of which a local signer can assert credibly. A signed local receipt
carries a different fact: "these gate rows were observed PASS against this exact
tree, by this key holder". The two compose rather than substitute. The right reading
is that the receipt is the *evidence* half of an attestation whose *provider-state*
half must still be recomputed on the runner (F7). The broker already models exactly
this split, with `review_evidence_broker_authenticated:false` naming the weaker half;
a v4 receipt should carry an equivalent, explicitly-false field rather than implying
verification it does not perform.

### 4.2 `pr-admission.yml` (670 lines, 1 job, `workflow_dispatch`-only)

Name: `Protected integration convergence admission` (`:1`). It admits an
integration-convergence artifact, not a PR merge, and is a different lane from the
required contexts. Relevant shared mechanics: `actions/checkout` pinned by sha
(`:54`); provider-resolved `base_sha` with a hard structural assertion that the
merge commit's parents are exactly `"$base_sha $head_sha"` (`:93-97`); a
`manifest_blob_sha` folded into per-row evidence records (`:389`); an 8-hour expiry
on issued evidence (`:201-208`, `date -u -d '+8 hours'`); and a final
"Attest exact convergence receipt and provider evidence" step (`:637`). It confirms
the house style — schema-tagged JSON, blob-sha binding, explicit expiry, provider
re-resolution immediately before emission — that a v4 receipt should match.

### 4.3 `scripts/check/check-self-review-guidance.shs` (138 lines)

A documentation-parity gate, not a security gate. It asserts that **22 "full"
surfaces** (`:18-36`: guides, `.agents/`, `.codex/`, `.claude/`, `.gemini/` skill and
command files, and their `examples/05_stdlib/spipe/` mirrors) each contain all ten
tokens `GitHub forbids`, `APPROVED`, `SPipe Self Review Admission`, `default`,
`deny`, `constrain`, `file`, `directory_files`, `directory_recursive`, `expiry`; and
that **4 further surfaces** (`:52-56`) carry a smaller token set. Verdict line at
`:138`.

The implication is a real, non-obvious implementation cost: **introducing a new
admission path means editing 26 documentation surfaces in the same change**, or this
gate goes red. It has no `--selftest` and no non-vacuity check, so it is weaker than
the F9 contract — worth noting, not worth fixing in this lane.

---

## 5. Prior art in this repo for signed and attested evidence

### 5.1 `check-external-must-check-receipt.shs` — an openssl-signed receipt verifier that already exists

This is the most important find, and the brief does not mention it. 338 lines. It is
the `mode=external-receipt` validator named by 21 manifest rows (`must_check_gates.sdn:57-77`).
It already implements, in POSIX sh, essentially the architecture F4 proposes:

- a schema-tagged evidence artifact — `evidence_schema simple.must-check-external-evidence/v2`
  (`:122`) — bound to `gate_id`, `source_fingerprint` and `final_verdict PASS`
  (`:123-125`), with a per-gate `acceptance_contract` and a fixed `acceptance_ids`
  list per gate (`:93-116`, `:126-127`);
- a **cryptographic signature check**: `openssl dgst -sha256 -verify
  "$work/reviewer.pem" -signature "$work/reviewer.sig" "$artifact"` (`:149`);
- a **trust-root policy file**, `config/check/must_check_external_reviewers.sdn`
  (`:9`), schema `simple.must-check-reviewer-policy/v1`, rows
  `|key_id, public_key_path, public_key_sha256|`, with the row required to match the
  receipt's `reviewer_key_id` exactly once (`:144`, `n != 1` ⇒ `reviewer-not-trusted`);
- **signer/producer separation**: `[ "$producer_id" != "$reviewer_key_id" ] ||
  fail reviewer-must-be-independent` (`:134`);
- ordering discipline stated in a comment at `:136-138`: reviewer authority is
  established *before* any external attachment is loaded or any gate-specific
  checker is invoked.

Two consequences for this design.

**(a) The sshsig choice must be justified against this in-repo openssl path, not
only against cosign/in-toto.** Both `ssh-keygen` and `openssl` are present on GitHub
ubuntu runners and on developer machines, so availability does not discriminate. The
honest discriminators favouring sshsig for v1 are: (i) **namespace binding** —
`ssh-keygen -Y sign -n simple-ci-receipt` makes the signature valid only for that
purpose, so a receipt signature can never be replayed as a signature over some other
artifact; `openssl dgst -sha256 -verify` signs raw bytes with no purpose separation,
and the current design compensates only by validating the artifact's schema line
after the fact. (ii) **A standard trust-root format** — `allowed_signers` is an
OpenSSH-defined file with principal patterns and `valid-after`/`valid-before` key
lifetimes, where the repo's `.sdn` policy table has no expiry column. (iii)
**Principal identity** — `-I <identity>` binds the signature to a named signer that
the verifier must supply, rather than to a key path the receipt itself names. The
openssl path remains the better model for *structure* (schema fields, trust table,
independence check) and should be mirrored; the primitive differs.

**(b) The existing pattern loads the trusted key from the tree under test**, via
`load_head_blob "$_key_path" "$_key_sha"` at `:147` reading `HEAD:` blobs. That is
precisely the F6 attack when the "tree under test" is a PR head: a PR could add its
own key file and its own policy row. It is safe *today* only because this validator
runs locally against a bootstrap HEAD, never on a runner over PR content. A CI
verifier must read the allowed-signers file from the **base ref**, and must not
accept any key path the receipt names.

**The trust table is empty.** `config/check/must_check_external_reviewers.sdn` is
5 lines: comment, header, schema, and the `trusted_reviewers |key_id,
public_key_path, public_key_sha256|` row header with **zero rows**. So this entire
signed-evidence mechanism is built, wired to 21 manifest rows, and provisioned with
no keys — nothing can pass it. That is the state to extend, and it is also evidence
that "provisioning a key is a reviewed repository change" (the file's own comment)
is already the accepted governance model here.

### 5.2 `simple.must-check-gate-receipt/v1`

`check-bootstrap-must-pass.shs:128-155`. `key=value` grammar via `receipt_field()`,
fields `receipt_schema`, `gate_id`, `final_verdict`, `source_fingerprint`,
`artifact_path`, `artifact_sha256`. Directly reusable as the ancestor of a v4
schema; its `artifact_path`/`artifact_sha256` indirection is the part to drop (see
§3's lesson on paths the verifier dereferences).

### 5.3 `src/lib/common/crypto/ed25519.spl` and `src/os/services/evidence/`

`ed25519.spl` is 26,988 bytes and exports (`:759-761`) `pure_ed25519_keypair_from_seed`,
`ed25519_pubkey`, `pure_ed25519_sign`, `pure_ed25519_verify`,
`pure_ed25519_self_test`, and `PureEd25519SeedSignatureV1` /
`pure_ed25519_sign_from_seed_v1`, backed by `ed25519_field.spl` and
`ed25519_scalar.spl`. This is **raw Ed25519 over a message**, not the SSHSIG wire
format. A pure-Simple twin verifier (F4's documented upgrade path) therefore needs
more than the existing primitive: an SSHSIG blob parser — `SSHSIG` magic, version,
public-key blob, namespace, reserved, `hash_algorithm`, and the sha512 prehash of
the message wrapped in the signed-data envelope. Record that as scope, not as a
one-line binding.

`src/os/services/evidence/` holds `capability_ledger.spl` (30,477 bytes),
`ledger_transition.spl` (4,061) and `admission_gates.spl`.
`simpleos_evidence_prepare_ledger_transition` is a pure, non-authorizing preparation
of one verified ledger row, with `SIMPLEOS_LEDGER_MAX_ROWS` and
`SIMPLEOS_LEDGER_MAX_CONSUMED_NONCES` bounds and explicit nonce consumption —
i.e. a bounded, anti-replay, append-only ledger design. It is **kernel-side SimpleOS
code requiring `bin/simple`**, so none of it runs on a runner. What transfers is the
shape: bounded row counts, explicit nonce/replay handling, and a "prepare then
atomically commit" split. What does not transfer is any of the code.

### 5.4 Already in flight in this worktree

`scripts/check/verify-local-ci-receipt.shs` (583 lines) is present as an **untracked**
file (`git status --porcelain` ⇒ `?? scripts/check/verify-local-ci-receipt.shs`); it
is not in `origin/main`. It implements schema `simple.local-ci-receipt/v1` with a
fixed 8-line header (`schema`, `tier`, `tree`, `manifest_sha`, `signer_identity`,
`session_id`, `signed_at_utc`, `rows`), `row: <id> <status>` lines required to be in
strict ascending id order, and an `end: <schema>` terminator, with the verdict
grammar of F9 (`PASS — <n> row(s) verified, receipt binds tree <sha> (signer <id>)`
at `:60`, `FAIL —` at `:64`, `ERROR — nothing was checked (<reason>)` at `:68`) and
`--selftest`. It reads the manifest as `git show <tree>:config/check/must_check_gates.sdn`
(`:45-47`, `:156-159`) rather than from the working tree. This document treats it as
the sibling implementation lane, not as settled truth; where the two disagree, the
plan resolves it.

---

## 6. Manifest readers — the constraint F8 must clear

`grep -rl must_check_gates scripts/ .github/ src/` returns five consumers plus the
manifest's own guards. Their parse shapes decide whether F8's "new column" or "new
tier" is viable:

| reader | how it parses | effect of a 7th column | effect of a new `ci` tier |
|---|---|---|---|
| `check-push-must-pass.shs:157,162` (awk `-F,`) | selects `bootstrap,` rows, reads `$5` | none — `$5` unchanged | none — row not selected |
| `check-push-must-pass.shs:295-296` (`while IFS=, read … _description`) | selects `push,` rows; last var absorbs the tail | none — lands in unused `_description` | none — row not selected |
| `check-bootstrap-must-pass.shs:82-84` `manifest_rows()` | selects `bootstrap,` rows | none | none |
| `check-caret-suite-bootstrap.shs:135-137` | `grep -Fq` on a literal row prefix ending at the command | none — substring still present | none |
| **`src/app/sj/gate_manifest.spl:61,66`** | `if fields.len() != 6:` → malformed; `if tier != "push" and tier != "bootstrap"` → invalid | **every row becomes "malformed mandatory gate row"** | **every row becomes "invalid mandatory gate tier"** |

`gate_manifest.spl` is reached from `src/app/sj/integrate_plan.spl:222` via
`parse_gate_manifest`, feeding `plan_protected_gate_manifest` (`:232`), which builds
the pinned protected-gate invocation plan; that function additionally rejects any
mode outside `range`/`ref`/`tree` (`:88-94`).

**This is the single hardest constraint found, and it applies to both F8 options.**
A 7th column breaks the strict `fields.len() != 6` check; a `ci` tier breaks the
closed tier allowlist. Either change must land together with an edit to
`gate_manifest.spl` (and to `plan_protected_gate_manifest`'s mode allowlist if a new
mode is introduced), or `sj`'s protected integration planning silently classifies
the entire manifest as malformed. `check-plan-acceptance-swept.shs:285` additionally
hard-codes the six-column header line in a selftest fixture, so that fixture moves
too.

Given both options break the same reader, the tie is broken elsewhere: a **new
`ci` tier** leaves all four sh readers untouched by construction (they select on
`push,` / `bootstrap,` prefixes) and adds no rows to the ledger's id-set equality
check (`manifest_count != ledger_count`, `:192`, counts bootstrap rows only), whereas
a 7th column perturbs the byte layout of all 74 existing rows. The `ci` tier is the
smaller blast radius.

**Verdict grammar is not uniform across the guards a receipt would cover.**
`check-cpu-hotloop-idiom.shs` prints `cpu_lane_hotloop_ok=true`, not a
`PASS — <n> … checked` line (measured, §7). A receipt writer must therefore key row
status on **exit status**, never on parsing stdout.

---

## 7. Measured signing and gate costs

`ssh -V` on this host: `OpenSSH_10.3p1, OpenSSL 3.6.2 7 Apr 2026` — well above the
8.0 floor F4 requires. Round trip performed 2026-09-06 in a scratch directory:

```
ssh-keygen -t ed25519 -N '' -C probe@simple-ci -f k
ssh-keygen -Y sign -f k -n simple-ci-receipt r.txt              # 0.037 s wall
ssh-keygen -Y verify -f allowed -I probe@simple-ci \
           -n simple-ci-receipt -s r.txt.sig < r.txt            # rc 0
# then append one byte to r.txt and re-verify:
                                                                # rc 255
```

- Signature file: **314 bytes**, armoured `-----BEGIN SSH SIGNATURE-----` PEM.
- Signing cost: **37 ms**. Verification is the same order. Signing is free relative
  to everything else in this design.
- **A tampered payload exits 255, not 1.** The verifier must test `[ "$rc" -eq 0 ]`;
  any construction that treats "not 1" as success, or that reads the status through
  a pipe, is fail-open here (F9).
- The `allowed_signers` line format used was `<principal> <keytype> <base64>`; the
  principal supplied to `-I` must match, which is what gives the receipt a named
  signer identity rather than an anonymous key.

F4's claim that `ssh-keygen` is present on GitHub ubuntu runners is taken from the
brief; it was **not** measured here (this is a macOS host, and no workflow in the
tree invokes `ssh-keygen` — `grep -rn ssh-keygen scripts/ .github/` returns nothing,
so sshsig would be entirely new to this repo). F4's requirement that CI assert
`ssh -V >= 8.0` once and FAIL rather than skip is what closes that gap.

**Gate cost, locally.** Three of the 27 idiom guards, run from this worktree with
`rg` available at `/opt/homebrew/bin/rg`:

| guard | exit | wall | last stdout line |
|---|---|---|---|
| `check-guard-wiring.shs` | 0 | 38 s | `PASS — 1557 guard(s) checked, 400 invoked, 1138 orphaned` |
| `check-no-dangling-reexports.shs` | 0 | 54 s | `PASS — 0 _partN re-export(s) … across 9101 module(s)` |
| `check-cpu-hotloop-idiom.shs` | 0 | 4 s | `cpu_lane_hotloop_ok=true` |

96 s for 3 of 27 on this host, against 172 s for all 24 steps on a Linux runner.
**Do not extrapolate this to a total.** Three points cannot be averaged over a set
whose members range from a 4-second grep to a 9101-module closure walk, and the
sample is biased toward the ones cheap enough to run safely during research. The
honest statement is: the full local set is unmeasured, three of its members cost
96 s here, and the number that matters — whether the full set finishes inside the
8.9-minute main cadence — is open. Measuring it is the first task of the plan lane,
because §8 turns on it.

---

## 8. Honest limits

**What a locally-signed receipt proves, and what it does not.** It proves that the
holder of a key listed in the base ref's allowed-signers file emitted a document
asserting that a named set of manifest rows was observed PASS against an exactly
named tree, and that the document has not been altered since. It does **not** prove
the gates ran, that they ran on that tree, that they ran unmodified, that their
output was read correctly, or that the machine that ran them was not lying. A
developer who runs nothing and hand-writes `row: push-guard-wiring pass` produces a
receipt that is cryptographically perfect and factually false. This is the same
trust class as `review-admission.yml`'s `self_attestation`, whose input description
says in the workflow file itself that it "is not independent authentication"
(`:24`), and whose evaluation request carries
`review_evidence_broker_authenticated:false` (`:286`). A v4 receipt should carry an
equivalent explicitly-false field so that the trust class is machine-readable and
cannot be lost in a summary. **Signing upgrades "some file in the PR says PASS" to
"a specific accountable person says PASS"; it does not upgrade either to "the gates
passed".** Every claim in the design and plan documents must be phrased at that
level.

The mitigations that stay meaningful are exactly the ones that are cheap enough to
run server-side on every head regardless (F7): signature and allowed-signer check,
tree and manifest-sha recompute from the head the runner is actually testing,
manifest↔receipt id-set and per-id cross-check, and the existing cheap structural
guards. Those are verification. The row verdicts are attestation. The design must
not blur them.

**Rebase and tree-churn cost.** `main` takes 162 commits per 24 h — one every
8.9 minutes. The ruleset is strict-up-to-date (`strict_required_status_checks_policy
== true`, asserted at `review-admission.yml:224`), so every PR must rebase onto the
new tip, and every rebase changes `<head>^{tree}` — 22 distinct root trees in the
last 30 commits. A tree-bound receipt is therefore invalidated by every rebase and
must be regenerated after the *final* one. Meanwhile `invalidate-pr-event`
(`:43-67`) resets the admission check on every `synchronize`, and the broker's own
decision expires after 600 s (`:257`). The consequence is a race: the author must
re-run the covered gate set, re-sign, push, and get the check reported before main
moves again. Whether that race is winnable is **unmeasured** (§7) and is the single
biggest open risk to the feature being useful rather than merely correct. If the
full local set exceeds ~9 minutes, the receipt lane trades one unwinnable race
(35-minute CI queue) for another, and the plan must say so and propose a narrower
covered row set rather than claiming a win.

Note also that a receipt covering only the idiom gate does not shorten the merge
path on its own: the second required context is the admission broker, which is
already the *only* thing completing on PRs #380 and #394. The win is that the idiom
gate stops being an unbounded wait; it is not a win on the admission race.

**If a signing key leaks.** The holder of a leaked key can produce a valid receipt
for any tree, for any row set the covered tier allows, indefinitely. Three properties
make this worse than it first looks:

1. `signed_at_utc` is **signer-controlled** and unauthenticated. It cannot bound
   validity, and a verifier that rejects "old" receipts on that field is trivially
   defeated by writing a newer timestamp. Freshness, if wanted, must come from a
   fact the signer does not control — the tree sha, which the runner recomputes.
2. Revocation is a commit to the base ref removing the key's line from the
   allowed-signers file. That is the correct mechanism (it inherits the repo's
   existing "provisioning a key is a reviewed repository change" governance, stated
   in `must_check_external_reviewers.sdn`'s own header comment), but it takes effect
   only for verifications that happen after the commit lands — and landing a commit
   on `main` is itself subject to the queue this feature exists to work around.
3. Because the receipt only ever *skips* work that CI would otherwise do, the blast
   radius is bounded by which rows the covered tier contains. A leaked key cannot
   make a red gate green on a row it does not cover, and cannot touch the
   server-side half of §7's mitigation list.

The sshsig-native mitigation is `valid-before` in the `allowed_signers` entry, which
bounds a key's lifetime at the *verifier*, using the verifier's clock rather than the
signer's claim. Treat a mandatory `valid-before` on every provisioned key as a v1
requirement candidate, and record the rotation interval as an open decision rather
than assuming one.

---

## 9. State of the art

Written from general knowledge as understood 2026-09-06; **not fetched** (network
access is blocked in this environment), so treat version-specific details as
unverified. The discriminator applied to each is the same: it must work on a GitHub
ubuntu runner with **no `bin/simple`** and **no external service dependency**.

**SLSA provenance / in-toto attestations.** in-toto defines a signed statement
binding a predicate (what was done) to subjects (artifact digests); SLSA layers a
provenance predicate and a set of build-integrity levels on top. This is the closest
conceptual match to what is wanted — a signed claim about how an artifact came to be
— and its subject/predicate split maps cleanly onto tree-sha/row-verdicts. Its
higher levels, however, derive their value from the *builder* being a trusted,
isolated service that the claimant cannot influence; a developer laptop is
explicitly the untrusted case those levels exist to exclude. Using the format
without that property would import its vocabulary and its implied assurance while
delivering neither. Verification also normally means a policy engine plus a
DSSE-envelope library on the runner: not `bin/simple`, but not nothing either.
**Verdict for here:** the right target for a v2 *format*, if the runner-side
tooling cost is paid; wrong for v1, and its assurance vocabulary must not be
borrowed for a laptop-signed claim.

**Sigstore / cosign.** Keyless signing with short-lived certificates from Fulcio,
bound to an OIDC identity, with inclusion recorded in the Rekor transparency log.
The identity binding is genuinely stronger than a static key, and transparency makes
key misuse discoverable rather than merely revocable. But keyless verification
contacts external services, and the whole model presumes an OIDC identity the signer
holds — which on a developer laptop is a human's account, not the build. It also
adds a binary to install on the runner. **Verdict for here:** rejected for v1 on the
external-service rule alone; the transparency-log idea is worth revisiting if
receipts ever become load-bearing enough that undetected key misuse is the dominant
risk.

**GitLab / Buildkite signed pipelines.** Both address a real adjacent problem —
ensuring the pipeline definition that runs is the one that was authorized, so a
job cannot be rewritten by the change it is testing. Buildkite signs job payloads
with a shared or asymmetric key verified by the agent; GitLab's equivalents bind
pipeline configuration and job identity. This repo solves the same problem
differently and adequately, with `pull_request_target` plus `ref: main` checkout
plus a `$GITHUB_WORKFLOW_REF` pin (`review-admission.yml:134-138`, `:185-186`).
**Verdict for here:** platform-native to CI systems this repo does not use; the
*principle* (the definition comes from the trusted ref, never from the change) is
already implemented and is F6.

**Bazel remote execution and result caching.** An action is keyed by a hash of its
inputs, command line and environment; a cache hit means "this exact action already
produced this exact output". This is the most rigorous answer to "can I skip work
that was already done" and needs no signature at all, because the key *is* the
evidence. Two things block it here. It requires a cache server, and the guards are
not hermetic actions — they are shell scripts scanning a whole worktree, with no
declared input set, so an action key cannot be computed honestly. More
fundamentally, a cache hit proves an action's *output bytes*, not a *verdict* about
a repository; the receipt needs to assert the latter. **Verdict for here:** the
input-hashing discipline is what `source_fingerprint` (§3) already gropes toward,
and is the correct long-term direction if the guards are ever made hermetic; not
available now.

**Why sshsig for v1.** It needs `ssh-keygen` and a file. No service, no daemon, no
network, no installed binary beyond what OpenSSH already provides, no `bin/simple`.
It gives purpose separation via `-n <namespace>` (which raw `openssl dgst` does not),
a named principal via `-I`, and a standard trust-root file format with key lifetimes
(`valid-before`) that the repo's existing `.sdn` reviewer table lacks. Measured cost
is 37 ms and 314 bytes (§7). It is a deliberately small mechanism for a claim whose
trust class is deliberately modest (§8) — pairing a heavyweight supply-chain format
with a laptop attestation would misrepresent the guarantee, which is the failure
mode this whole document is trying to avoid.

---

## 10. Open questions for the design and plan lanes

1. **Does the covered gate set run locally inside the 8.9-minute main cadence?**
   Unmeasured (§7). Everything about the feature's usefulness turns on it.
2. **`ci` tier vs. 7th column** — both break `src/app/sj/gate_manifest.spl:61,66`
   (§6). The tier has the smaller blast radius, but the `sj` edit is mandatory either
   way and must land in the same change.
3. **Which of the 26 uncovered idiom guards get manifest rows**, and in what order.
   All-or-nothing coverage is not required: F8's per-row rule means an uncovered row
   simply runs.
4. **Key lifetime and rotation interval** for `valid-before` (§8).
5. **Whether the receipt reuses `source_fingerprint` as a secondary binding.** It
   costs 0.26 s and cross-checks against existing bootstrap machinery, but it does
   not cover `.github/` and must never be the authority (§3).
6. **26 documentation surfaces** must be updated with the new admission path or
   `check-self-review-guidance.shs` goes red (§4.3).
7. **`repo-hygiene.yml`'s four `if: ${{ !cancelled() }}`-less gate steps** (§1) —
   an independent one-line-per-step fix that should not be bundled into this lane.

---

## Provenance

Directory note: `doc/01_research/infra/` held 9 entries before this file; with
`local_ci_receipt/` it holds 10, which is the documented ceiling. Any further
research topic under `doc/01_research/infra/` needs a reorganisation first.

All measurements taken 2026-09-06 from a detached worktree at
`4699194f81e34f4dad7af088e9b8d24c375c5568`, on macOS (Darwin 25.5.0, arm64) with
`rg` at `/opt/homebrew/bin/rg` and `OpenSSH_10.3p1`. GitHub API figures via `gh`
against `ormastes/simple` at approximately 04:35Z. No bootstrap, no compile, and no
write outside the worktree was performed.
