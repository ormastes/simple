# Local CI receipt + signing — detail design

Status: DESIGN. Nothing here is built. Written 2026-09-06 against `origin/main`
`4699194f81e`. Facts F1-F10 in the task brief are measured and are treated as
binding inputs, not re-litigated.

**One-sentence statement of what this is.** A developer who runs the idiom /
structural ratchet gates locally signs a small SDN document binding *which work*
(jj change-ids) and *which bytes* (git tree) the gates were run against; CI
verifies that signature against a committed allowed-signers list read from the
BASE ref, recomputes the binding against the head it is actually testing, and —
when everything matches — reports the required `Code Idiom & Structural Ratchet
Gates` check green after running only a ≤60 s conflict-damage sanity set instead
of all 47 gate steps.

**Trust class, stated up front and not softened (F7).** A dev-key signature
proves **WHO** produced the receipt. It does **not** prove **THAT** the gates
ran, nor that they ran honestly. This is the same trust class as
`review-admission.yml`'s `self_attestation` input, whose own description in the
workflow reads "this is not independent authentication". Everything in §7 and
§11 exists because that sentence is true. A reader who takes away "CI now
verifies the idiom gates cryptographically" has misread this document.

**Implementation already in flight.** A parallel lane has
`scripts/check/verify-local-ci-receipt.shs` in this worktree (untracked as of
writing) implementing the verifier under the same schema id, the same namespace
`simple-ci-receipt`, and the same allowed-signers path
`config/check/ci_receipt_allowed_signers`. This document uses those names. Where
this design and that script disagree, the disagreement is a real defect in one of
them and must be resolved, not papered over — the script is not the specification.

---

## 1. Problem

- **F1**: exactly two checks are required to merge —
  `Code Idiom & Structural Ratchet Gates` and `SPipe Self Review Admission`
  (ruleset `spipe-vcs-v3-main`; `branches/main/protection` is 404, rulesets are
  the enforcement surface). The idiom job is therefore the only *merge-blocking*
  CI cost this feature can remove. Skipping any of the other ~30 optional checks
  is a runner-capacity win only.
- The idiom job (`code-idiom-gates` in `.github/workflows/repo-hygiene.yml`,
  display name `Code Idiom & Structural Ratchet Gates`) has **47 `- name:` steps**
  (counted 2026-09-06), each `if: ${{ !cancelled() }}` so one red gate does not
  mask the rest. Wall-clock cost of the job is **unmeasured** here; it is
  dominated by ~47 whole-tree ripgrep scans over a 109k-file tree.
- **F3**: the machinery is half-built. `config/check/must_check_gates.sdn` is the
  manifest; `doc/08_tracking/check/must_check_db.sdn` is the ledger
  (`simple.must-check-ledger/v3`); `validate_ledger_text()` in
  `scripts/check/check-push-must-pass.shs` already does manifest↔ledger id-set
  equality and **per-id command byte-match** with a fail-closed arm. **No
  workflow reads any of it** (`grep -rln must_check .github/workflows/` is
  empty). That gap is the feature.

### 1.1 The required gate is effectively non-functional today (measured)

This reframes the feature from *optimization* to *repair*, and it is the single
strongest argument for it. Measured over `repo-hygiene.yml`'s last **60 runs**:

| outcome | runs |
|---|---|
| success | **0** |
| cancelled | 26 |
| queued (never started) | 24 |
| failure | 10 |

The last success was **2026-09-03**: **172 s of execution after 2112 s queued** —
**92 % queue**. The mechanism is `cancel-in-progress: true` on
`concurrency: ${{ github.workflow }}-${{ github.ref }}`
(`repo-hygiene.yml:10-12`) against **162 commits/24 h** on `main`: each new commit
cancels the in-flight run for the same ref, and the job's own runtime exceeds the
inter-commit interval.

Consequences this design must carry:

- A **required** merge check that has not reported success in 60 runs is not
  protecting anything; it is a merge blocker that clears only by luck. Whatever
  else this feature does, a ~60 s `sanity` path may be the only way this context
  ever reports success under the current commit rate.
- §9.0's concurrency-key change is therefore not a footnote about
  `pull_request_target` — it is a repair in its own right, and it should land
  even if every other part of this design is abandoned.
- Conversely: **do not claim this feature's benefit is "saving 47 gate steps".**
  The measured cost is overwhelmingly *queue*, not *execution* (2112 s vs 172 s
  on the one datapoint we have). The benefit is that a short job survives
  cancellation windows that a long one does not.

### 1.2 One accuracy note that must not be conflated

`.github/` is **outside** the 8-root `source_fingerprint` used by the ledger. The
existing fingerprint therefore **cannot** detect a workflow edit. In this design
the `tree` binding is the only thing that can. Nowhere may `source_fingerprint`
be described as covering the workflow, and the receipt deliberately does not
reuse it.

**Goal (F2, explicit user directive).** A verified receipt covering the idiom
rows and bound to the tree under test lets that job report success without
running the gates. Not advisory. Implemented.

---

## 2. Decisions, decision-first

| # | Decision | Beat | Why |
|---|---|---|---|
| D1 | Receipt is a **separate document** `simple.local-ci-receipt/v1` that *references* the manifest by `manifest_sha`. It is **not** ledger v4. | Extending `simple.must-check-ledger/v3` to v4 | The ledger is a **tracked file**. A per-PR receipt committed into the tree it attests is circular: writing it changes the tree, which changes `tree`, which invalidates the receipt. It also makes every PR touch `doc/08_tracking/check/`, i.e. a guaranteed conflict on a repo where 8 sessions land concurrently and main moves every 5-10 min. §3.1. |
| D2 | Receipt lives in a **git note under `refs/notes/ci-receipts`, keyed by the TREE object**, not by a commit. | PR comment; workflow artifact; a per-tree ref | §6. |
| D3 | **sshsig** (`ssh-keygen -Y sign/verify`), namespace `simple-ci-receipt`. | (a) the **existing in-repo `openssl dgst` verifier** `check-external-must-check-receipt.shs`; (b) a pure-Simple ed25519 verifier | (a) is the real contender and is argued at length in §10.0 — namespace binding, principal identity and key expiry are the discriminators, and the existing path has none of the three. (b) is blocked: CI runners have no `bin/simple` (F4); `src/lib/common/crypto/ed25519.spl` is the documented **upgrade path** (§13), not built now. |
| D4 | Verdict is **three modes** — `full` / `sanity` / `escalate` — not a binary skip. | Binary skip vs run | CI tests a *merge*, not the tree the developer signed. Merge-introduced damage is invisible to the signature. §7. |
| D5 | Receipt binds **both** a jj `change_id` set and a git `tree`. | Binding a commit sha; binding a tree only | Change-id = *what was reviewed* (survives rebase/amend/force-push). Tree = *which bytes were reviewed*. §8. |
| D6 | Per-row granularity via a **new `ci` tier only** — no new manifest column at landing. `ci_job` / `inputs` are a deferred extension, needed only when a second CI job participates or when real per-row input sets exist. | Adding columns now; a separate mapping file; a global skip flag | One source of truth (F8). A new *tier* perturbs **no existing row's bytes** and adds nothing to the ledger's `manifest_count != ledger_count` equality; a new *column* rewrites every row and forces `validate_ledger_text`'s awk and its selftest to move together. Both options require editing the same Simple reader (`src/app/sj/gate_manifest.spl:61`, `:66`), so that cost does not discriminate. §5. |
| D7 | Everything the decision depends on is read from **BASE**, never from the PR head. | Reading head | Otherwise a PR adds its own signing key or edits the verifier / workflow to always skip (F6). §9. |
| D8 | Rollback is a **repo variable**, not a revert commit. | Reverting the workflow | One click, no merge queue, no rebase storm. §13. |

---

## 3. Receipt schema `simple.local-ci-receipt/v1`

### 3.1 Why a separate document, not ledger v4

Three independent reasons, any one sufficient:

1. **Circularity.** The ledger is tracked. Writing a receipt into it mutates the
   tree the receipt attests. There is no fixed point.
2. **Conflict magnet.** Every PR would touch `doc/08_tracking/check/must_check_db.sdn`.
   With strict-up-to-date enforcement and a base that moves every 5-10 min, that
   file becomes the serialisation point for the whole repo.
3. **Different lifetime and different trust.** The ledger records *bootstrap*
   state, is long-lived, and is reviewed. A receipt is per-tree, ephemeral, and
   is attested by a single developer key. Merging two trust classes into one
   schema forces the ledger's reviewers to reason about signatures they did not
   ask for.

What is reused instead (F3, do not write a second parser): the manifest-parse +
id-set + per-id command byte-match half of `validate_ledger_text()` is factored
out into `validate_rows_against_manifest(manifest, rows, tier)` — same awk, one
new `tier` parameter selecting the row regex (`,bootstrap,` / `,push,` / `,ci,`).
The receipt's `local_ci_receipt_results` block uses the **same `id, status,
command` grammar** as the ledger's results block precisely so the same awk
validates both. `check-push-must-pass.shs` keeps calling it with `tier=bootstrap`
and its behaviour must be byte-identical afterwards; its selftest is the proof.

### 3.2 Fields

Header block `local_ci_receipt:` — all values double-quoted strings, emitted in
exactly this order:

| field | type | source | meaning |
|---|---|---|---|
| `schema` | literal | — | exactly `simple.local-ci-receipt/v1`. Any other value ⇒ `full`. |
| `repo` | `owner/name` | `ormastes/simple`, a constant in the signer | Cross-repo replay defence (§11). |
| `tree` | 40 lowercase hex | `git rev-parse <rev>^{tree}` | Which **bytes** were gated. Content, not commit sha: shas churn under rebase, trees do not (F5). |
| `manifest_sha` | 40 lowercase hex | `git rev-parse <rev>:config/check/must_check_gates.sdn` | Blob sha of the manifest **as of that tree**. Pins the row set and every row's command text. |
| `session_id` | token | the SPipe/agent session identifier | Audit join key to the local run's logs. Free-form but constrained by §4's character rules. |
| `signed_at_utc` | `YYYY-MM-DDTHH:MM:SSZ` | `date -u +%Y-%m-%dT%H:%M:%SZ` | Same format the ledger already validates. Used for staleness policy (§9.4), never for trust. |
| `host` | token | `uname -n` | Where the gates ran. Audit only. |
| `signer_identity` | token | the principal in the allowed-signers file | Passed verbatim to `ssh-keygen -Y verify -I`. |

Block `local_ci_receipt_changes |change_id|` — one row per jj change-id in the
attested set (§8). Zero rows is an **ERROR at sign time**, never an empty
receipt.

Block `local_ci_receipt_results |id, status, command|` — one row per manifest row
the local run covered:

| field | type | meaning |
|---|---|---|
| `id` | `[a-z0-9][a-z0-9-]*` | Must exist in the manifest. At sign time that means the manifest at `manifest_sha`; at verify time the cross-check is against the **tested** manifest's `ci` rows — see input **M** in §7.1 for why. |
| `status` | `pass` \| `fail` | Only `pass` is usable; `fail` is recorded honestly and forces `full` for the covering job. **The vocabulary is deliberately these two.** The ledger awk's row regex is `(pass\|todo\|blocked\|fail)`; a `skipped` status would not match it and would be silently dropped by the very parser §3.1 reuses. If a third status is ever needed, the status alternation in the factored `validate_rows_against_manifest` must become a parameter, changed together with both selftests. |
| `command` | quoted string | Must **byte-match** the manifest row's command at `manifest_sha`. |

**A row's verdict is the command's EXIT STATUS, never a parsed verdict line.**
The 27 guard scripts behind the idiom job do **not** share a verdict grammar —
`check-cpu-hotloop-idiom.shs`, for instance, prints `cpu_lane_hotloop_ok=true`,
not the `PASS — <n> … checked` line that `.claude/rules/vcs.md` describes for the
push guards — and only **1 of the 27** is in the manifest at all today. A signer
that tried to parse verdict lines would need 27 dialects and would silently
mis-read the 26 it does not know. The signer therefore records `pass` iff the
command exited 0 and `fail` otherwise, reading the status **directly into a
variable on the line after the command, never through a pipe** (F9). The
consequence is honest and worth stating: a guard that exits 0 while printing a
failure verdict would be recorded as `pass` — that is a defect in *that guard*,
and it already mis-reports to CI today for the same reason, so the receipt
inherits the existing trust level rather than lowering it.

### 3.3 Example (illustrative values; `…` marks elision)

```
local_ci_receipt:
  schema: "simple.local-ci-receipt/v1"
  repo: "ormastes/simple"
  tree: "ed3f2bb31645e118d0b238c91d93aec6758c69df"
  manifest_sha: "9f1c0b7a2d3e4f5061728394a5b6c7d8e9f00112"
  session_id: "spipe-2026-09-06T09:14:02Z-4f2a"
  signed_at_utc: "2026-09-06T09:41:17Z"
  host: "ormastes-mac"
  signer_identity: "ormastespp@gmail.com"
local_ci_receipt_changes |change_id|
    yxxsmlzoyurlrnxmrtlmvzkopmpnpmns
    zqltrvknsupwmxoyzrlkmtpqrsvwxyzb
local_ci_receipt_results |id, status, command|
    ci-idiom-cpu-hotloop, pass, "sh scripts/check/check-cpu-hotloop-idiom.shs"
    ci-idiom-ui-backend-isolation, pass, "sh scripts/check/check-ui-backend-isolation.shs"
    ci-idiom-tui-standalone-closure, pass, "sh scripts/check/check-tui-standalone-closure.shs"
    ci-idiom-guard-wiring, pass, "sh scripts/check/check-guard-wiring.shs"
    …
```

---

## 4. Canonical serialization — the exact bytes that get signed

The signer emits the payload with a **pure function of its inputs**: given the
same `(tree, manifest_sha, repo, session_id, signed_at_utc, host,
signer_identity, change-id set, result rows)`, the output bytes are identical.
`signed_at_utc` and `host` are *inputs*, not ambient state read at emit time —
that is what makes a byte-asserting selftest fixture possible and resolves the
apparent contradiction between "contains a timestamp" and "deterministic".

Rules, all mandatory:

1. **Encoding**: US-ASCII only. Any byte outside `0x20`-`0x7E` (plus the LF
   separators emitted by the writer) in any field is an **ERROR at sign time**.
2. **Line endings**: LF (`0x0A`) only. Never CRLF.
3. **Trailing newline**: exactly one LF terminates the last line. No blank lines
   anywhere, including at the end.
4. **No comments.** The payload carries none, ever. (The manifest and ledger do;
   the signed payload does not, so a comment can never change signed bytes.)
5. **Header**: line `local_ci_receipt:` then the eight fields in the §3.2 order,
   each as `  <key>: "<value>"` — two spaces indent, one space after the colon,
   value always double-quoted, no trailing whitespace.
6. **Changes block**: header line `local_ci_receipt_changes |change_id|`, then
   one row per change-id as four spaces + the bare id. **Order: ascending ASCII
   byte order**, deduplicated. A set has no intrinsic order; sorting is what
   makes the serialization of a set reproducible.
7. **Results block**: header line `local_ci_receipt_results |id, status, command|`,
   then one row per result as four spaces + `<id>, <status>, "<command>"` —
   separator is exactly comma + one space; `id` and `status` bare; `command`
   double-quoted. **Order: manifest order** — the order the `ci`-tier rows appear
   in `config/check/must_check_gates.sdn` at `manifest_sha`. This matches
   `validate_ledger_text`'s existing `manifest_order[]` iteration, so verifier and
   hook agree by construction.
8. **Forbidden field characters**: `"` (0x22), `,` (0x2C), TAB, LF, CR. There is
   **no escaping mechanism**; a field containing one of these is an **ERROR at
   sign time**, not an escaped value. This is safe today: the parsers are `awk -F,`
   and every existing manifest command is already comma-free (verified across all
   78 manifest lines). Introducing an escape would require changing both existing
   parsers and is not worth it.

### 4.1 What is EXCLUDED from the signed payload, and why

| Excluded | Why |
|---|---|
| the signature itself | detached; see §6.3 for the split rule |
| commit sha, branch name, PR number | churn under rebase and force-push; identity is carried by `change_id` + `tree` (§8) |
| `evidence` / `evidence_sha256` | large, path-dependent, and unverifiable by CI — CI has no access to the developer's log files. Including them would create a field the verifier must ignore, which is worse than absence. |
| `owner`, `unblock_condition`, `description` | ledger/manifest bookkeeping; not facts about this run. `description` in particular is prose that gets reworded, which would invalidate receipts for no reason. |
| durations, exit codes, stdout | not part of the claim being made; unbounded size |
| ledger `source_fingerprint`, `completed_at_utc` | bootstrap state, unrelated to this tree |
| any comment line | see rule 4 |

---

## 5. Per-row granularity — manifest changes (F8)

### 5.0 Tier first, columns later (D6)

**At landing the manifest header does not change at all.** The only edit is new
rows carrying the new tier value `ci` in column 2. Reasoning, decision-first:

- A new tier **perturbs no existing row's bytes**. A new column rewrites all 78
  lines, and every rewritten line is a line `validate_ledger_text`'s per-id
  command byte-match must still agree on.
- A `ci` row adds **nothing** to the ledger: `validate_ledger_text`'s
  `manifest_count != ledger_count` equality counts only `,bootstrap,` rows, so
  `ci` rows neither require ledger entries nor perturb the count. A column, by
  contrast, forces the awk and its selftest to move together (§5.2) — a
  same-change edit to a parser that gates every push.
- **The Simple-side reader must change either way**, so it does not
  discriminate: `src/app/sj/gate_manifest.spl:61` hardcodes `fields.len() != 6`
  (a 7-field row is classified "malformed mandatory gate row") and `:66` accepts
  only `push`/`bootstrap` (a `ci` row is "invalid mandatory gate tier"). The tier
  option needs one predicate widened at `:66`; the column option needs `:61` *and*
  the field indexing after it. The tier option is the smaller edit even here.
- What is lost by deferring the columns: `ci_job` and `inputs`. Neither is needed
  at landing. `ci_job` is only necessary once a **second** CI job consumes
  receipts — with one consumer, `tier == ci` *is* the mapping, and the consumer
  is named in one place (the workflow). `inputs` only feeds `escalate`, which is
  inert until real per-row input sets exist (§7.3), so declaring a column of `*`
  for every row buys nothing.

**If the columns land anyway** — an implementation lane in this worktree has
already written
`|id, tier, push_blocking, mode, command, ci_job, inputs, description|` — that is
acceptable and this design ratifies the layout, subject to §5.1's invariant. The
sequencing preference above is a preference about *risk ordering*, not a
correctness claim; both layouts implement the same semantics. What is **not**
negotiable is the invariant.

### 5.1 The deferred columns and their position

Current header:

```
must_check_gates |id, tier, push_blocking, mode, command, description|
```

New header (this is the layout the in-flight implementation lane has already
written into `config/check/must_check_gates.sdn` in this worktree; this design
ratifies it):

```
must_check_gates |id, tier, push_blocking, mode, command, ci_job, inputs, description|
```

**Position: `ci_job` and `inputs` are inserted AFTER `command`, pushing
`description` to column 8. The load-bearing invariant is not "append at the end"
— it is: NO COLUMN MAY EVER BE ADDED AT OR BEFORE `command`.** That invariant
binds whenever these columns land, whether now or later.

- `validate_ledger_text()` reads `manifest_blocking[id]=trim($3)` and
  `manifest_command[id]=unquote($5)`. Inserting after `command` leaves `$3` and
  `$5` untouched. Inserting a column anywhere at or before `command` silently shifts `$5` and turns
  every per-id command byte-match into a mismatch — i.e. it would fail every push
  with "ledger is malformed", the exact failure mode the BSD-awk incident already
  produced once.
- `run_manifest_push_gates()` does `while IFS=, read -r _id _tier _blocking _mode
  _command _description`. POSIX `read` assigns the **remainder** to the last
  variable, so with the new layout `_description` receives
  `<ci_job>, <inputs>, "<description>"`. `_description`
  is never used in that function (the `case` matches on `"$_id:$_mode:$_command"`),
  so this is harmless — but it must be **stated in a comment at that loop**, or the
  next reader will "fix" it. If that loop ever needs a real `description`, it
  must gain the two intervening variables explicitly — never re-order columns.

Both parsers change together with their selftests. Specifically:
`validate_ledger_text`'s selftest gains a fixture whose manifest carries the two
new columns and must still produce a byte-identical command match; and a negative
fixture where a column is inserted *before* `command`, which must FAIL. Without
the negative fixture the ordering constraint above is prose, not enforcement.

### 5.2 Column semantics

- **`ci_job`** — quoted. The **YAML job key** of the CI job the row belongs to,
  e.g. `"code-idiom-gates"`. **Not** the display name (`Code Idiom & Structural
  Ratchet Gates`) — that contains `&` and spaces, is presentation, and is edited
  more freely than the key. Empty string `""` = the row maps to no CI job (every
  existing push/bootstrap row).
- **`inputs`** — quoted, space-separated repo-relative path prefixes the row's
  gate reads, or the literal `*` meaning "declared unbounded — reads the whole
  tree". Used only by `escalate` mode (§7.3). An **absent or unparseable** value is
  *undeclared*, which is not the same as `*` and collapses the mode to `full`.

### 5.3 The new `ci` tier

New tier value `ci`, alongside `push` and `bootstrap`. It is invisible to both
existing parsers by construction: `validate_ledger_text`'s manifest arm anchors on
`,[[:space:]]*bootstrap,` and `run_manifest_push_gates`'s awk on
`,[[:space:]]*push,`. A `ci` row therefore adds no ledger obligation and no push
dispatch case, so it cannot trip the fail-closed `*)` arm.

**At least 47** new `ci` rows are added — one per `run:` **command**, not per
step, so a step with several commands (e.g. the four LLM setup-contract gates in
one step) contributes several rows. 47 is the `- name:` step count measured
2026-09-06 and is a lower bound on the row count.

Every `ci` row's `inputs` additionally carries the implicit prefixes
`scripts/check/` and `config/check/` — a change to a gate script or to the
manifest changes what the gate does, regardless of what the gate reads.

### 5.4 Guard wiring, and one new guard

`check-guard-wiring.shs` computes reachability from hooks and workflows to guard
*scripts*; it does not enumerate manifest rows. A `ci` row's guard is already
reached through its `run:` step in `repo-hygiene.yml`, so **no new arm is needed
there**. (Verify this before implementing — it is read from the script's structure,
not from a run: `sh scripts/check/check-guard-wiring.shs` must still be green
after the manifest edit, and that run is the evidence.)

What *is* needed is a new push-tier guard, because nothing otherwise keeps the
manifest's `ci` rows honest:

- **`scripts/check/check-ci-receipt-row-parity.shs`** — asserts a bijection between
  the `ci`-tier rows whose `ci_job` is `code-idiom-gates` and the `run:` command
  lines of that job in `.github/workflows/repo-hygiene.yml`, byte-for-byte. A row
  whose command differs from the workflow's would let a receipt attest something
  CI would never have run. Verdict line last on stdout; `PASS — <n> row(s)
  checked, 0 divergent` / `FAIL — …` / `ERROR — nothing was checked`; 0 rows is
  ERROR; `--selftest` runs first and is fatal (fixtures: matched set ⇒ PASS; a row
  whose command text differs by one byte ⇒ FAIL; a workflow step with no row ⇒
  FAIL; a row with no step ⇒ FAIL; empty workflow ⇒ 0 checked ⇒ caller ERRORs).

Manifest row (columns 7/8 empty — it is a push guard, not a CI-covered row):

```
    push-ci-receipt-row-parity, push, true, tree, "sh scripts/check/check-ci-receipt-row-parity.shs", "manifest ci rows byte-match the repo-hygiene idiom job run: lines", "", ""
```

and the byte-matching dispatch case in `run_manifest_push_gates`:

```
'push-ci-receipt-row-parity:tree:sh scripts/check/check-ci-receipt-row-parity.shs')
    run_push_gate "$_id" "$_blocking" "$ROOT/scripts/check/check-ci-receipt-row-parity.shs" || { rm -f "$_push_rows"; return 1; } ;;
```

---

## 6. Where the receipt lives

### 6.1 Chosen: git note under `refs/notes/ci-receipts`, keyed by the TREE object

```
git notes --ref=ci-receipts add   -F <payload+sig> <tree>     # attach
git notes --ref=ci-receipts show  <tree>                      # read, O(1)
git push origin refs/notes/ci-receipts                        # publish
```

Git notes attach to **any** object, not only commits. Keying by the tree is the
right key because the tree *is* half the binding (§3.2) — the runner computes
`git rev-parse <head_sha>^{tree}` and looks the note up directly; there is no
search and no ambiguity when several commits share a tree.

Honest cost: `refs/notes/ci-receipts` is a single shared ref. With 8 concurrent
sessions it is a non-fast-forward magnet — each publisher must
`git fetch origin refs/notes/ci-receipts` and, on rejection,
`git notes --ref=ci-receipts merge -s cat_sort_uniq refs/notes/origin/ci-receipts`
and retry. That is a real operational cost and the signer script must implement
the retry loop (bounded, 5 attempts, then ERROR — never silent).

Ruleset caveat, applying **equally to both options**: `refs/notes/ci-receipts`
is itself a ref outside `refs/heads/`, so whatever the ruleset says about
creating or updating non-branch refs constrains the chosen design as much as the
alternative below. This is **unmeasured**; the evidence that settles it is named
in §14.

**Alternative kept on the table: one ref per receipt,
`refs/ci-receipts/<tree>`.** It never conflicts (each ref is created once and
never updated) and a missing receipt is a clean `git fetch` failure. It was not
chosen as the default only because **whether the `spipe-vcs-v3-main` ruleset
permits creating refs outside `refs/heads/` is unmeasured**. The evidence that
would settle it: `gh api repos/ormastes/simple/rulesets/21573643` → the `rules`
array's `creation`/`update` entries and the ruleset's `ref_name` include pattern.
If notes-ref contention proves worse than expected, switch to this; the receipt
format and verifier are unchanged, only the fetch step differs.

### 6.2 Rejected alternatives

| Option | Rejected because |
|---|---|
| A tracked file (ledger v4, or a new `doc/08_tracking/check/receipts/`) | Circular and a conflict magnet — §3.1. |
| Workflow artifact | Artifacts are produced *by a CI run*. The receipt is produced *by the developer, before the PR exists*. Cross-workflow artifact reads need an API token in a `pull_request_target` job, and an artifact uploaded by a PR-triggered run is attacker-controlled content in the same trust position as the head checkout. |
| PR comment | Mutable after the fact by anyone with write access; requires a token in the verifying job to read *and* trust; Markdown mangles the payload's exact bytes, and §4 depends on exact bytes. |
| Commit trailer in the commit message | Changes the commit, therefore changes nothing about the tree — but message edits are routine under `jj describe`, and a message is not a place to put a 400-byte armored signature. |

### 6.3 Payload / signature split (byte-exact, or it breaks)

`ssh-keygen -Y sign` writes a **detached armored** signature. The note body is
the concatenation `payload || signature`. The split rule for the verifier:

> Scan the note body for the **first line exactly equal to**
> `-----BEGIN SSH SIGNATURE-----`. Everything strictly before that line —
> including its terminating LF — is the payload, verbatim. Everything from that
> line to the end is the signature.

The verifier feeds those **exact bytes** to `ssh-keygen -Y verify` on stdin. It
must never re-serialize the parsed payload and verify that: a re-canonicalization
that drifts by one newline produces a signature failure that looks like an
attack. Parsing the payload into fields is done **after** verification, from the
same bytes.

---

## 7. The mode decision (supersedes any binary skip/run reading)

CI does not test the tree the developer signed. It tests a *merge* of the PR head
with a base that moves every 5-10 min. Damage introduced **by the merge itself**
was never seen by the local run and is invisible to the signature. That is why
`sanity` is not empty and why `escalate` exists.

### 7.1 Decision inputs

All computed on the runner, all from BASE-supplied code (§9):

- **R** — a receipt exists for the tested tree, its signature verifies against the
  BASE `allowed_signers` under namespace `simple-ci-receipt`, and `schema` and
  `repo` match.
- **C** — the attested `change_id` set equals the tested `change_id` set (§8).
- **T** — attested `tree` equals the tested tree.
- **M** — the `ci`-tier rows for the covered job are byte-identical between the
  **BASE** manifest and the **TESTED** manifest, and the receipt's row set is
  exactly that id set with byte-identical commands.
  **Note the deliberate relaxation:** M is *not* `attested manifest_sha == tested
  manifest blob sha`. Two reasons. (a) That blob may not exist on the runner at
  all — same unreachability problem as the attested tree (§7.3 step 0) — so a
  binding that requires fetching it is not implementable in the common rebase
  case. (b) Blob equality also fails whenever an unrelated **push**- or
  **bootstrap**-tier row lands on main, which happens constantly and has nothing
  to do with the idiom gates; that would force `full` on essentially every
  rebase. Comparing the `ci` rows *for the covered job* is both implementable and
  the property actually needed. `manifest_sha` stays in the payload as an audit
  field and as the anchor for the honesty argument, not as a runtime equality
  test.
- **I** — id-set and per-id command cross-check passes against the manifest at
  `manifest_sha`, and **every** row mapped to the covered `ci_job` is present with
  `status = pass`.

`M`'s second clause is not redundant with the first: without it, a PR edits the
manifest to replace a gate's command with `true`, runs the trivialized gate
honestly, signs honestly, and the receipt verifies. Comparing against BASE closes it.

### 7.2 The table

| R | C | T | M ∧ I | mode | what runs | budget |
|---|---|---|---|---|---|---|
| no | * | * | * | **full** | all 47 gate steps | today's cost |
| yes | mismatch / unreadable / absent | * | * | **full** | all 47 | today's cost |
| yes | match | yes | yes | **sanity** | §7.4 set only | **≤ 60 s** |
| yes | match | yes | no | **full** | all 47 | today's cost |
| yes | match | no | yes | **escalate** | sanity set + path-selected gates (§7.3) | sanity + selected |
| yes | match | no | no | **full** | all 47 | today's cost |

**The line that guarantees fail-closed.** The verifier's mode selection is a
single `case` whose final arm is `*) mode=full ;;`, in the same style as
`run_manifest_push_gates`'s fail-closed `*)`. `sanity` and `escalate` are reached
only by an explicit arm matching an exhaustively-enumerated positive condition.
Any input the verifier cannot classify — unreadable note, malformed payload,
`ssh-keygen` non-zero for any reason, a `git` command that fails, an unparseable
`ssh -V` — falls through to `*)` and lands in `full`. **A verifier that cannot
decide is a failure, never a pass** (F6).

The verifier reads every exit status **directly into a variable on the line after
the command**, never through a pipe (F9): a pipeline's `$?` is the last stage's
status and has produced false greens in this repo before.

### 7.3 `escalate` — same work, different bytes

Reached when the change-id set matches but the tree does not, i.e. *the reviewed
work was rebased*. Blindly falling to `full` here throws away a perfectly good
review every time main moves — which, at 5-10 min, is most of the time.

**Precondition that is easy to miss: the attested tree may not exist on the
runner.** Pushing `refs/notes/ci-receipts` ships the note's own blobs, not the
object the note is *attached to*. After a rebase or force-push the attested tree
is usually unreachable from any pushed ref and is therefore absent from the
runner's clone. The procedure below states exactly what happens then; it does
not assume the object is there.

Procedure:

0. Try to materialize the attested tree. The receipt MAY carry an optional
   `attested_commit` field, which is a **fetch hint only** and is explicitly
   **not** part of the identity (§4.1 excludes commit shas from identity for
   churn reasons; a hint that is wrong or stale costs a `full` run and nothing
   else). Attempt `git fetch --no-tags origin <attested_commit>` when present,
   then `git cat-file -e <attested_tree>^{tree}`; read the exit directly.
   **If the attested tree cannot be materialized, the mode is `full`.** That is a
   real, common degradation, stated rather than hand-waved: until the hint field
   and a receipt-publishing convention that keeps the attested commit reachable
   both exist, `escalate` degrades to `full` for most rebases.
1. `changed=$(git diff --name-only <attested_tree> <tested_tree>)`. Empty ⇒
   contradiction with T=false ⇒ `full`.
2. Select every `ci` row for the covered job whose `inputs` either (a) is `*`,
   or (b) contains a prefix `P` such that some changed path starts with `P` (plain
   prefix match on `/`-boundaries; no globbing, no regex — a glob dialect is one
   more thing to get wrong).
3. Run the §7.4 sanity set **plus** exactly the selected rows' commands.
4. **Undeclared inputs collapse to `full`.** If any `ci` row for the covered job
   has an absent, empty, or unparseable `inputs`, the mode becomes `full`. An
   undeclared input set is unknown, and unknown must never resolve toward less
   work.

**Honest starting position:** at landing, every `ci` row is expected to declare
`inputs: "*"`, because most of these gates ripgrep the whole tree. With all
rows `*`, `escalate` re-runs every row and is therefore *equivalent to `full`*.
The value of `escalate` appears incrementally as individual rows declare real
input prefixes (e.g. the freestanding-runtime gates plausibly read only
`src/runtime src/os`; the UI isolation gate only `src/app/ui src/lib/skia`).
Declaring a row's inputs is a per-row change with a per-row proof obligation —
the declaration is wrong if the gate reads a path outside it — and is deliberately
**not** part of this design's initial scope.

### 7.4 The `sanity` set and its 60 s budget

Hard design constraint: **≤ 60 s wall clock**. This mode must not grow into a
mini-full-run. Contents, and nothing else:

| step | what it catches | cost |
|---|---|---|
| `ssh -V` floor assert (§ 9.3) | unusable toolchain | negligible |
| sshsig verify + allowed-signer check | forged / unknown-signer receipt | negligible (one ed25519 verify) |
| tree + `manifest_sha` recompute against the head under test | receipt bound to different bytes | two `git rev-parse`, negligible |
| change-id set recompute + compare | receipt bound to different work | one `git cat-file` per commit in the PR, negligible |
| manifest↔receipt id-set + per-id command cross-check | trivialized or drifted row set | one awk pass over 78 + N lines, negligible |
| `sh scripts/check/check-no-conflict-tree-push.shs <range>` | jj conflict trees (a conflict commit's tree contains only `.jjconflict-*`; a clone gets an empty repo) | **unmeasured**; described in `.claude/rules/vcs.md` as a cheap range guard |
| `sh scripts/check/check-no-conflict-markers-push.shs <range>` | literal conflict-marker text injected by a rebase into file **content** without the commit being tree-conflicted — the 2026-07-30 incident wrote markers into 38 tracked files including the Rust seed | **unmeasured**, cheap |
| `sh scripts/check/check-tree-size-push.shs <range>` | structurally wrong tree — main was wiped to 4 files twice in 24 h with every other guard green (`118c636ead8`) | **unmeasured**, cheap; note its `--selftest` (14 fixtures) runs first and is fatal |

These three guards are exactly the merge-damage class the signature cannot see,
they already exist, and they are already trusted enough to block every push. Their
individual wall-clock costs are **unmeasured** — `.claude/rules/vcs.md` describes
them as light range guards but records no number, and inventing one here would be
worse than the gap. **First implementation task: measure all three on this repo and
record the numbers in this section.** If their sum plus checkout exceeds 60 s, the
budget is violated and the design must be revisited — do not silently drop a guard
to make the number.

**Checkout is the real budget risk and needs an explicit decision.** The three
range guards need both range endpoints resolvable. `fetch-depth: 0` on a 109k-file
repo is likely to eat the whole budget on its own (**unmeasured**). The
implementation therefore does a shallow `actions/checkout` and then
`git fetch --no-tags --depth=50 origin <base_sha> <head_sha>`; if the range
`<base_sha>..<head_sha>` cannot be resolved at that depth, the verifier deepens
once to `--depth=500`, and if it still cannot resolve, it **falls to `full`**.
Failure to establish the preconditions for a cheap check is never a pass.

---

## 8. Binding to jj changes, not commits (D5)

**Measured fact, 2026-09-06, this repo.** jj writes the change-id as a real
header *inside* the git commit object. `git cat-file commit HEAD` on `origin/main`
prints, between `committer` and the message:

```
change-id yxxsmlzoyurlrnxmrtlmvzkopmpnpmns
```

So a runner that has only `git` — **no `jj`** — reads it with
`git cat-file commit <sha> | awk '/^change-id /{print $2; exit}'`. That is what
makes this implementable at all.

### 8.1 Both, because they answer different questions

- `change_id` — **what** was reviewed. Stable across rebase, amend and
  force-push. jj's whole point.
- `tree` — **which bytes** were reviewed. Changes whenever content changes,
  including under a rebase that resolves differently.

Neither alone is sufficient. Change-id alone lets rebase-introduced content
through unchecked. Tree alone discards a valid review every time main moves.

### 8.2 A PR is a set of commits

The receipt binds a **set**. Canonical serialization: deduplicated, sorted in
ascending ASCII byte order, one per line in the `local_ci_receipt_changes` block
(§4 rule 6). Change-ids are lowercase `[k-z]`-alphabet reverse-hex tokens of fixed
length, so byte order is a total order and the sort is stable and locale-free —
the signer sets `LC_ALL=C` for it.

### 8.3 Which revs are read, on both sides

- **Local (signing).** The set is `git rev-list <base>..<head>` where `<head>` is
  the exact commit being offered and `<base>` is its merge-base with
  `main@origin`. `tree` is `git rev-parse <head>^{tree}`.
- **CI (verifying).** GitHub tests a *synthesized merge commit*
  (`refs/pull/N/merge`). The verifier does **not** read change-ids or the tree from
  that merge commit — the merge commit is created by GitHub, has no change-id, and
  its tree is not the head's. It reads:
  - `head_sha = github.event.pull_request.head.sha`,
  - `base_sha = github.event.pull_request.base.sha`,
  - tested tree = `git rev-parse ${head_sha}^{tree}`,
  - tested change-id set = the change-id header of every commit in
    `git rev-list ${base_sha}..${head_sha}`.

  **Why the head tree is the right thing to compare, not the merge tree:** the
  `spipe-vcs-v3-main` ruleset enforces strict up-to-date. At merge time the head
  already contains the base, so the merge tree equals the head tree. A head that
  is *not* up to date fails the up-to-date requirement independently and cannot
  merge regardless of what this verifier says. The remaining window — head is
  up to date now, base advances before merge — forces a rebase, which changes the
  head sha, re-triggers CI, and re-enters this decision at `escalate` or `full`.
- **A commit with no `change-id` header** (authored by plain `git`) is not an
  error to paper over: the receipt cannot bind it. If any commit in the tested
  range lacks the header, **C is false and the mode is `full`.** State this in the
  verifier's output so the developer knows why.

### 8.3.1 Two operational preconditions

- **`jj squash` / `jj split` change the change-id set.** Reshaping a PR's
  commits therefore invalidates the receipt via input **C** and yields `full`.
  That is correct — the set of reviewed changes really is different — but it
  surprises people, so the verifier prints which ids were expected and which were
  found.
- **`git.write-change-id-header` must stay enabled** in the repo's jj config.
  If it is ever turned off, new commits carry no header, C is false, and every PR
  falls to `full`. Safe, but it silently disables the whole feature; the signer
  asserts the header is present on every commit it binds and ERRORs otherwise
  (§10.1).

### 8.4 Force-push

A force-push preserves change-ids **by design** — that is what change-ids are for.
Consequence, stated plainly: a signed receipt remains valid across a force-push of
the same change, and **the tree comparison is the only thing standing between that
and content substitution.** If the force-push changed content, T is false and the
mode is `escalate`, not `sanity`; if it changed nothing, `sanity` is correct. This
gets its own threat-model row (§11).

---

## 9. CI integration — the idiom-gate skip (F2, the primary deliverable)

### 9.0 Concurrency key — must change with the trigger

This is also the repair of §1.1's measured pathology (0 successes in 60 runs, 26
of them cancelled), so it stands on its own merits independently of receipts.

`repo-hygiene.yml` currently declares
`concurrency: group: ${{ github.workflow }}-${{ github.ref }}` with
`cancel-in-progress: true`. Under `pull_request_target`, `github.ref` is
`refs/heads/main` for **every** PR, so all PRs collapse into one concurrency
group and cancel each other's *required* check. The key becomes:

```
group: ${{ github.workflow }}-${{ github.event.pull_request.number || github.ref }}
```

Same family of trap: under `pull_request_target`, `github.sha` is the BASE
commit, not the head. Nothing in this job may use `github.sha` to mean "the code
under test" — §8.3's `head.sha` / `base.sha` are the only correct sources.

### 9.1 Trigger and checkout

`code-idiom-gates` moves from `pull_request` to **`pull_request_target`**, which is
what makes "the workflow file, the verifier, and the allowed-signers list all come
from BASE" true — the same reason `review-admission.yml` already uses it (F6).

`pull_request_target` runs BASE's workflow with a **writable** token by default
and with repository secrets available, so checking out head code under it is the
classic pwn-request. The `full`/`escalate` fallback paths **must** run HEAD's
`scripts/check/*.shs` against HEAD's tree — running BASE's gate scripts against
HEAD's tree would fail every PR that legitimately edits a gate or its baseline.
Required mitigations, all of them:

- job-level `permissions: { contents: read }` — nothing else, no `write` anywhere;
- **zero `secrets.*` references** anywhere in the job (enforce with a grep-based
  selftest in `check-ci-receipt-row-parity.shs`, so it is a gate, not a promise);
- head checked out from `refs/pull/${{ github.event.pull_request.number }}/head`
  at the pinned `head.sha`, with `persist-credentials: false`, into its own
  directory;
- **every decision input** materialized from BASE, never from the checkout —
  the verifier, `config/check/ci_receipt_allowed_signers`,
  `config/check/ci_receipt_revoked_keys`, `scripts/check/check-ci-receipt-row-parity.shs`,
  and the three structural sanity guards of §7.4 with any helper files they
  source (materialize the whole `scripts/check/` directory from BASE into
  `$RUNNER_TEMP` rather than cherry-picking files, since
  `check-tree-size-push.shs` and friends may source siblings). The sanity guards
  are decision inputs, not diagnostics: a HEAD-supplied `check-tree-size-push.shs`
  is a HEAD-supplied verdict. `check-ci-receipt-row-parity.shs` runs **here, in
  the sanity set, from BASE** — not only as a push-tier guard: `.claude/rules/vcs.md`
  records that push guards are routinely nullified by `--no-verify`, so a push
  guard alone cannot be what keeps manifest↔workflow honest for a security
  decision;
- the verifier materialized from BASE, never from the checkout:
  `git show ${{ github.event.pull_request.base.sha }}:scripts/check/verify-local-ci-receipt.shs > "$RUNNER_TEMP/verify-local-ci-receipt.shs"`,
  and executed from `$RUNNER_TEMP`;
- likewise `config/check/ci_receipt_allowed_signers` and
  `config/check/ci_receipt_revoked_keys`, materialized from BASE into `$RUNNER_TEMP`.

**This is not a widening of exposure.** The job today already checks out and
executes PR-authored code, with a read-only token and no secrets. The three
bullets above hold it to exactly that, while moving the *decision* inputs out of
the attacker's reach.

### 9.2 Reporting success without running the gates

**Do not implement the skip as a skipped job.** A `needs:`/`if:` job-level gate
makes GitHub report the check as *skipped*; rulesets currently treat skipped as
passing, but that is a known footgun and one ruleset edit away from blocking every
PR. Instead the job **always runs**:

1. First step `receipt` is a **wrapper that always exits 0**, because a
   non-zero first step would paint every PR red on day one (the notes ref does
   not exist yet, which is the *normal* state, not a defect):

   ```
   mode=$(sh "$RUNNER_TEMP/verify-local-ci-receipt.shs" … )
   rc=$?
   [ "$rc" -eq 0 ] || mode=full
   case "$mode" in sanity|escalate) : ;; *) mode=full ;; esac
   printf 'mode=%s\n' "$mode" >> "$GITHUB_OUTPUT"
   ```

   The verifier itself keeps the F9 convention (verdict line last, ERROR = exit
   2); the wrapper is what turns *any* verifier outcome that is not an explicit
   `sanity`/`escalate` into `full`. It also sets `rows` (space-separated row ids
   to run, empty for `sanity`). On `github.event_name != 'pull_request_target'`
   — the `push:` trigger to `main` — the wrapper sets `mode=full` without
   consulting anything.
2. Every one of the existing gate steps changes its condition from
   `if: ${{ !cancelled() }}` to the **negated form**

   ```
   if: ${{ !cancelled() && !(steps.receipt.outputs.mode == 'sanity' || (steps.receipt.outputs.mode == 'escalate' && !contains(steps.receipt.outputs.rows, '<row-id>'))) }}
   ```

   **The negation is the whole point and must not be "simplified".** The
   obvious positive form `mode == 'full' || contains(rows, id)` is **fail-open**
   in the exact state this feature lands in: with `vars.CI_RECEIPT_SKIP_ENABLED`
   unset the `receipt` step is skipped, `steps.receipt.outputs.mode` is the empty
   string, `'' == 'full'` is false and `contains('', id)` is false — so **every
   gate step skips, the job reports green, and zero gates run.** In the negated
   form an empty mode matches no positive arm, so the step runs. A gate can only
   be suppressed by an explicit, positive `sanity`/`escalate` value. This also
   preserves the `!cancelled()` property that the long comment at
   `repo-hygiene.yml:48-64` exists to protect.
3. The sanity guards run as their own steps, conditioned on
   `mode != 'full'`.
4. A final step always runs and prints the verdict: mode, signer identity, tree,
   change-id count, and — for `sanity` — the list of row ids the receipt covered
   and the sentence "gates NOT executed; covered by verified receipt". Exit 0.

The check therefore reports an explicit green with a visible, auditable reason,
never an ambiguous "skipped".

### 9.3 The `ssh -V` precondition

```
ssh_v=$(ssh -V 2>&1)
rc=$?
```

`ssh -V` prints to **stderr**; `2>&1` is mandatory. Parse `OpenSSH_(\d+)\.(\d+)`.
Requirements: `rc` must be 0, the string must parse, and major must be ≥ 8 (`-Y
sign`/`-Y verify` and `namespaces=` land in 8.0). Local `ssh -V` is
`OpenSSH_10.3p1`, ample (F4). **This precondition FAILS, it never skips** — a
runner that cannot verify signatures produces `mode=full` and says so on stdout;
it never produces `sanity`.

### 9.4 Staleness

`signed_at_utc` is **not** used for trust and **not** used to expire receipts —
the binding, not the clock, is what makes a receipt valid, and a tree that has not
changed is a tree whose gate verdicts have not changed. It is recorded for audit
and printed in the verdict. A receipt older than 30 days is printed with a
`stale-receipt` note in the verdict line but is still honoured; if operational
experience says otherwise, tighten it then, with the incident as evidence.

### 9.5 Fork PRs

A fork contributor cannot push to `refs/notes/ci-receipts` on this repo. Their PRs
therefore always land in `mode=full`. That is correct — an external contributor's
key is not in the allowed-signers file either — and it must be stated in the
verdict output rather than looking like a malfunction.

---

## 10. Sign and verify — exact commands

### 10.0 Why sshsig and not the signed-receipt verifier this repo already has

**A working signed-receipt verifier with a trust-root table already exists here,
and no design that ignores it is defensible.**
`scripts/check/check-external-must-check-receipt.shs:149` runs

```
openssl dgst -sha256 -verify <reviewer.pem> -signature <reviewer.sig> <artifact>
```

against the trust table `config/check/must_check_external_reviewers.sdn`
(schema `simple.must-check-reviewer-policy/v1`, rows
`|key_id, public_key_path, public_key_sha256|`, **currently zero rows**). It is
wired to **21 manifest rows** with `mode=external-receipt`, and it already has
schema binding, gate binding, fingerprint binding, and a per-gate acceptance-id
contract. It is not a sketch.

**What it does BETTER than this design, and the honest answer.** It enforces
`producer_id != reviewer_key_id` — the party who produced the artifact may not
be the party who signs off on it. That independence check is a genuinely
stronger idea than anything in §11's mitigations, and it is exactly what T8 (a
developer who signs without running the gates) lacks. **This design cannot adopt
it, and the reason is structural, not an oversight:** a *local* receipt has one
party. The developer runs the gates and signs; there is no second principal on
the machine. Requiring independence would mean requiring a second human to
counter-sign every PR's receipt, which is a review process, not a CI
optimization, and would cost more than the CI run it replaces. What the design
does instead is bound the damage — the server-side floor of §12 runs on every
PR regardless of receipt, and every receipt is attributable (principal, host,
session id, timestamp). **This is a real weakness relative to the external-receipt
path and is recorded as such in T8, not argued away.** If independence is ever
wanted here, the mechanism is that same `producer_id != reviewer_key_id` field,
and this design should be superseded rather than patched.

**The three discriminators that decide it for sshsig.** As far as this analysis
found, these are the *only* ones — everything else (hashing, ed25519, a committed
trust table, fail-closed parsing) either path gives you:

| capability | sshsig | `openssl dgst` |
|---|---|---|
| **Namespace / domain separation** (`-n simple-ci-receipt`) — a signature made for one purpose cannot be replayed as another | yes, cryptographically bound into the signed blob | **none**. A raw `dgst` signature is over bytes with no purpose label; any signature that principal ever made over the same bytes is interchangeable |
| **Principal identity** (`-I <identity>`, matched against `allowed_signers`) | yes; identity is an input to verification | **none**. The trust table maps `key_id` to a key *path*; identity is implied by which file you loaded, not by anything the signature says |
| **Key expiry / rotation window** (`valid-before=` / `valid-after=` in `allowed_signers`) | yes (version-gated — see §10.4, floor **unmeasured**) | **none**. Rotation is add/remove a row, with no notion of "receipts signed before date X are no longer honoured" |

Namespace binding is the decisive one for a *CI skip* specifically: this
signature authorizes suppressing a required check, so the ability to distinguish
it from every other signature that principal has ever made is not a nicety.

**Its flaw is the F6 attack in the wild, and is why §9.1 exists.** That verifier
loads *both* the signature and the reviewer's public key with `load_head_blob`
(`:140`, `:147`) — **from the tree under test**. On a push gate that is
survivable: the pusher already controls the working copy, and the guard is one
of many. **Copied onto a CI runner as-is it means a PR ships its own trust
root** — precisely T1. This is the concrete, in-repo precedent for the rule that
this design's `allowed_signers`, revoked-keys file, verifier and sanity guards
are all materialized from **BASE** (§9.1), and it should be read as a warning
about what happens when a trust root is loaded by the same helper that loads
untrusted artifacts.

### 10.1 Signing (local, `scripts/check/sign-local-ci-receipt.shs`)

Preconditions, all fatal (ERROR, never a signed receipt):

- The working tree is **clean and equals `HEAD^{tree}`**. `git status
  --porcelain` must be empty. The shared jj working copy is essentially never
  clean and 8 sessions land into it concurrently, so the signer is expected to run
  from a detached `git worktree add --detach <sha>` — exactly the isolation this
  design document itself was written under (F10).
- Every commit in `<base>..<head>` carries a `change-id` header (§8.3).
- Every field passes the §4 character rules.
- The gates actually ran in this invocation: the signer **runs the `ci`-tier
  commands itself** and records their real verdicts. It has no flag to accept
  hand-written verdicts. (This does not make the receipt trustworthy to CI — see
  §11 — but it removes the *accidental* stale receipt, which is the common case.)

```
ssh-keygen -Y sign -f "$SIGNING_KEY" -n simple-ci-receipt "$payload"
rc=$?
```

writes `$payload.sig`. The note body is `cat "$payload" "$payload.sig"`.

### 10.2 Verifying (runner, `scripts/check/verify-local-ci-receipt.shs`, materialized from BASE)

```
ssh-keygen -Y verify \
    -f "$RUNNER_TEMP/ci_receipt_allowed_signers" \
    -r "$RUNNER_TEMP/ci_receipt_revoked_keys" \
    -I "$signer_identity" \
    -n simple-ci-receipt \
    -s "$sigfile" < "$payloadfile"
rc=$?
[ "$rc" -eq 0 ] || { mode=full; }
```

`$signer_identity` comes from the payload — which is untrusted until `rc` is 0.
That is safe and is how sshsig is meant to be used: the identity selects *which*
principal line to check against, and a forged identity simply fails to verify. The
identity is additionally required to match `^[A-Za-z0-9._%+@-]+$` before being
passed to `-I`, so it cannot become an option.

### 10.3 `allowed_signers` file

Committed at **`config/check/ci_receipt_allowed_signers`** (next to the manifest,
in the same reviewed directory), read from **BASE** only:

```
# <principal> namespaces="simple-ci-receipt" <keytype> <base64> <comment>
ormastespp@gmail.com namespaces="simple-ci-receipt" ssh-ed25519 AAAAC3Nza... ci-receipt-2026-09
```

`namespaces="simple-ci-receipt"` is mandatory on every line: it means a key
admitted here can sign **nothing else** that this repo would honour, and a
signature made for another namespace (a git commit signature, say) cannot be
replayed as a receipt.

### 10.4 Rotation and revocation

- **Add**: append a line with a new comment tag (`ci-receipt-<yyyy-mm>`), in a
  reviewed PR. Because the file is read from BASE, the new key becomes usable only
  after that PR merges — a deliberate one-merge delay.
- **Retire**: move the line to **`config/check/ci_receipt_revoked_keys`** (an
  OpenSSH KRL or a plain list of public keys, passed via `-r`). Revocation is
  immediate on merge and applies to *already-signed* receipts, which
  add/remove-from-`allowed_signers` alone would not.
- `valid-after=` / `valid-before=` options are **deliberately not used**: the
  OpenSSH version that supports them in `-Y verify` is newer than 8.0 and the
  exact floor on `ubuntu-latest` is **unmeasured**. Evidence that would settle it:
  `man ssh-keygen` on the runner image, ALLOWED SIGNERS section. Until measured,
  time-scoping is done by the revoked-keys file. **The floor for `-Y verify -r`
  is itself unmeasured** — do not assume it is 8.0. Both floors must be measured
  on the actual runner image before the feature is enabled; whichever is higher
  becomes the §9.3 precondition, which FAILS rather than skips.

---

## 11. Threat model

Read §7's trust-class paragraph first. This table is honest about which rows are
*mitigated* and which are only *bounded*.

| # | Adversary | Capability | What stops them | Partial? |
|---|---|---|---|---|
| T1 | PR that adds its own signing key | edits `config/check/ci_receipt_allowed_signers` in the PR | **This is not hypothetical — the in-repo precedent is `check-external-must-check-receipt.shs:140,147`, which loads the reviewer signature *and the reviewer public key* with `load_head_blob`, i.e. from the tree under test (§10.0).** The verifier here reads that file from **BASE** (`git show <base_sha>:…`), never from the checkout. The PR's version is inert until it merges — and merging requires the required checks, which is the thing being protected. | No — fully mitigated, **conditional on** the `pull_request_target` + BASE-materialization discipline in §9.1 being implemented exactly. |
| T2 | PR that edits the workflow or the verifier to always skip | edits `.github/workflows/repo-hygiene.yml` or `scripts/check/verify-local-ci-receipt.shs` | Same mechanism: `pull_request_target` runs BASE's workflow, and the verifier is materialized from BASE's blob into `$RUNNER_TEMP`. HEAD's copies are never executed for the *decision*. | No — mitigated. But note it is only as strong as the reviewer of the PR that changes those BASE files; that is a human control. |
| T3 | Receipt replayed from a different tree | reuses a valid receipt for other content | `tree` recompute on the head under test. Mismatch ⇒ `escalate` (if change-ids match) or `full`. Never `sanity`. | No — mitigated. |
| T4 | Receipt replayed from a different repo (fork with the same signer) | copies a receipt from another repository | `repo` field in the signed payload. | **Partial**: a fork whose content is byte-identical yields the same tree, and a receipt for identical bytes is *legitimately* the same claim. The `repo` field stops the *label* being wrong, not the tree-equality case — and the tree-equality case is not an attack. |
| T5 | Stale receipt after rebase | signs, then rebases onto a moved base | Tree changes ⇒ T false ⇒ `escalate` (sanity set + path-selected gates), or `full` if any `inputs` is undeclared. | No — mitigated, and §7.3 is the reason this is not simply `full`. |
| T6 | Force-push preserving change-ids, substituting content | `jj` force-push of the same change with different bytes | Change-ids match by design, so **only the tree comparison stands between this and content substitution**. Different bytes ⇒ T false ⇒ `escalate`/`full`. | No — mitigated, but the mitigation is entirely the tree comparison; a design that dropped the tree binding and kept change-ids would be fully exploitable here. |
| T7 | Leaked developer key | signs arbitrary receipts as a trusted principal | Revoked-keys file (§10.4), merged to BASE, invalidates past and future receipts from that key. Detection is out of scope. Blast radius bounded by: the server-side floor (§12) still runs on every PR, and the *other* required check (`SPipe Self Review Admission`) is unaffected. | **Partial**. Until revocation merges, the holder can green the idiom check on arbitrary content. Nothing here detects the leak. |
| T8 | A developer who signs without running the gates | runs the signer with the gates faked, or patches their local signer | **Nothing stops this, and the design does not claim to.** This is F7: the signature proves WHO, not THAT. Bounded by: the server-side floor (§12), the manifest-vs-BASE comparison (T9), and the fact that it is attributable — the receipt names a principal, a host, a session id and a timestamp. | **Partial by construction.** Same trust class as `review-admission.yml`'s `self_attestation`, which self-describes as "not independent authentication". |
| T9 | PR trivializes a gate command, runs the trivial version, signs honestly | edits `config/check/must_check_gates.sdn` | Input **M**'s second clause: `ci` rows for the covered job must be **byte-identical between BASE and HEAD**. Any manifest edit touching those rows ⇒ `full`. | No — mitigated. Cost: a PR that legitimately edits an idiom gate always pays a full run. Correct trade. |
| T10 | Merge-introduced damage the local run never saw | lands a rebase that injects conflict markers, a conflict tree, or a truncated tree | The `sanity` set's three structural guards (§7.4), which run in **every** non-`full` mode against the actual head. These are the guards that caught the 2026-07-30 marker injection and would have caught the two 24-hour tree wipes. | No — mitigated for the three known damage classes. **Unknown merge-damage classes are not covered**; that is an accepted, stated residual. |
| T11 | Tampering with the shared notes ref | force-updates `refs/notes/ci-receipts` to attach a forged receipt to a tree | Requires push access; and the note body still has to carry a signature from an allowed, unrevoked key over the exact tree. A push-capable attacker can *remove* receipts (denial of service ⇒ `full` ⇒ safe). | **Partial**: no protection against a push-capable attacker with a valid key — that reduces to T7/T8. |

---

## 12. What stays server-side always, and its budget

Runs on the real head, in **every** mode including `sanity`, and can never be
turned off by a receipt (F7):

1. sshsig signature + allowed-signer + revoked-key check;
2. head `tree` and `manifest_sha` recompute;
3. change-id set recompute;
4. manifest↔receipt id-set and per-id command cross-check, plus the BASE-vs-HEAD
   `ci`-row byte comparison;
5. `check-no-conflict-tree-push.shs`, `check-no-conflict-markers-push.shs`,
   `check-tree-size-push.shs`.

**Budget: ≤ 60 s wall clock for the whole `sanity` path.** Item-by-item estimates
are in §7.4; items 1-4 are all sub-second by inspection (one ed25519 verify, four
`git rev-parse`, one `git rev-list` + one `git cat-file` per commit, one awk pass
over ~125 lines). **Item 5 and the checkout/fetch are unmeasured on this repo and
are the entire risk.** The first implementation step is to measure them; if the
total exceeds 60 s the design is revisited, not the guard list.

Also unchanged and unaffected: the other required check, `SPipe Self Review
Admission`. This design touches exactly one job.

---

## 13. Migration and rollback

**Landing order** (each step is independently revertible and green on its own):

1. Widen the tier vocabulary to accept `ci` — `src/app/sj/gate_manifest.spl:66`
   (and `:61`'s field count only if the columns land, §5.0) — with no header
   change and no existing row rewritten. Confirm `validate_ledger_text` and
   `run_manifest_push_gates` are byte-for-byte indifferent (their row regexes
   anchor on `,bootstrap,` and `,push,`), and add a selftest fixture containing a
   `ci` row that asserts exactly that indifference. **Nothing behaves differently
   yet.**
   *If and when the `ci_job`/`inputs` columns land instead or in addition:*
   update `validate_ledger_text`'s awk **and its selftest together** (§5.1),
   including the negative fixture that rejects a column inserted at or before
   `command`, and add the comment at `run_manifest_push_gates`'s `read` loop about
   `_description` receiving the remainder.
2. Add the 47 `ci`-tier rows and `scripts/check/check-ci-receipt-row-parity.shs`
   with its manifest row and byte-matching dispatch case; run
   `sh scripts/check/check-guard-wiring.shs` and confirm green.
3. Add `config/check/ci_receipt_allowed_signers`,
   `config/check/ci_receipt_revoked_keys`,
   `scripts/check/sign-local-ci-receipt.shs`, `scripts/check/verify-local-ci-receipt.shs`.
   Each new `.shs` follows F9: verdict line **last** on stdout
   (`PASS — <n> … checked` / `FAIL — …` / `ERROR — nothing was checked`),
   non-vacuity absolute (0 items checked = ERROR), `--selftest` that runs **before**
   every scan and is fatal, exit status read directly into a variable.
4. Change `code-idiom-gates` to `pull_request_target` with the §9.1 hardening and
   add the `receipt` step, **but gate the whole mechanism on a repo variable**:

   ```
   if: ${{ vars.CI_RECEIPT_SKIP_ENABLED == 'true' }}
   ```

   on the `receipt` step only. With the variable unset the step does not run,
   `steps.receipt.outputs.mode` is the empty string, and §9.2's **negated** step
   conditions therefore run every gate — an empty mode is not `sanity` and not
   `escalate`, so nothing is suppressed. That property is the reason for the
   negation and is the single line that makes this rollout safe.
   **Land with the variable unset.** For a period, run
   the verifier in report-only form (it prints the mode it *would* have chosen) and
   compare against reality before flipping.
5. Set `CI_RECEIPT_SKIP_ENABLED=true`.

**Rollback: unset the repo variable.** One click in repo settings, no commit, no
merge queue, no rebase storm, effective on the next job. This is why the kill
switch is a variable and not a revert — reverting a workflow under strict
up-to-date on a repo whose main moves every 5-10 min is itself a multi-hour
operation, which is exactly when you do not want it.

**Pure-Simple twin verifier — FUTURE WORK, NOT BUILT NOW (F4).**
`src/lib/common/crypto/ed25519.spl` exists. Once a full-CLI pure-Simple binary is
deployed to CI runners, `verify-local-ci-receipt.shs` gains a twin implemented in
Simple, and the two are cross-checked in the repo's existing dual-run style
(`scripts/check/check-dual-run-shadow.shs`) rather than one replacing the other.
Recorded here as a TODO with its precondition; no part of this design depends on
it.

---

## 14. Uncertainties, and the evidence that would settle each

| Uncertainty | Evidence that settles it |
|---|---|
| Wall-clock cost of the three structural guards and of checkout+fetch on this repo — the whole 60 s budget rests on it | Run them on `ubuntu-latest` against a real PR range and record the numbers in §7.4. |
| Whether `spipe-vcs-v3-main` permits creating refs outside `refs/heads/` (decides notes-ref vs per-tree-ref, §6.1) | `gh api repos/ormastes/simple/rulesets/21573643` → `rules[].type == "creation"` and the ruleset's `ref_name` include patterns. |
| Whether GitHub rulesets in this repo treat a *skipped* required check as passing | Irrelevant by design — §9.2 never produces a skipped job. Listed so nobody "simplifies" the design back into that dependency. |
| OpenSSH floor for `valid-after=`/`valid-before=` in `-Y verify` on `ubuntu-latest` (§10.4) | `man ssh-keygen` on the runner image; until then, revocation only. |
| Whether `check-guard-wiring.shs` stays green with `ci`-tier rows present (§5.4) | Run it after step 2 of §13. It computes reachability from workflows to guard scripts and should be indifferent, but that is inference, not a measurement. |
| Whether an independence check (`producer_id != reviewer_key_id`, §10.0) can be had for a *local* receipt without turning it into a second-human review | An operational proposal that names the second principal and its cost; absent that, T8's weakness stands as recorded. |
| OpenSSH floor for `-Y verify -r` (revoked-keys) on `ubuntu-latest` | `man ssh-keygen` / `ssh -V` on the runner image; this decides §9.3's precondition together with the `valid-before` floor. |
| Real per-row `inputs` for each of the 47 gates — without them `escalate` ≡ `full` (§7.3) | Per-row analysis of what each gate script actually reads; out of scope here, deliberately. |
| Contention rate on `refs/notes/ci-receipts` with 8 concurrent sessions | Operate it and count the retry-loop iterations the signer logs. |
