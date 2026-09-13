# Must-Check Tiering Feature Expert

Keep interactive push validation near ten seconds. Do not add compiler builds,
full tests, QEMU/hardware work, or benchmark campaigns to the push driver. Add
expensive requirements to `config/check/must_check_gates.sdn` and produce their
evidence through `check-bootstrap-must-pass.shs`.

Compiler Stage 1-4 rows are push-blocking and may be promoted only after the
Stage 2/3 full-provenance verifier and exact Stage 4 post-bootstrap acceptance
oracle pass. Bootstrap completion then runs every automated registry row and
records its retained log; do not require a second operator command. PASS needs
a UTC timestamp and evidence reference. TODO and blocked rows remain visible
and never count as PASS.

Ledger schema v3 adds `owner` and `unblock_condition`. Reject empty or
`unassigned` owners, TODO/blocked rows with `none` or empty unblock text, and
PASS rows whose unblock condition is not `none`. Focused transition evidence
must come from the bootstrap producer and then pass through the committed-ref
push consumer; a hand-authored PASS fixture is insufficient.

Production automated and compiler evidence is retained below
`doc/08_tracking/check/evidence/<source-fingerprint>/` and committed with the
ledger. The push consumer hashes the evidence blob from the exact pushed ref,
not the live checkout. Production recording refuses fingerprinted input drift
from `HEAD`. A receipt-backed TODO can earn its first durable PASS only through
`check-bootstrap-must-pass.shs --record-gate-pass <id> --evidence
<repo-relative-committed-receipt>`; carry-forward requires the identical
committed blob/hash. Source-sensitive automated rows still invalidate when the
fingerprint changes.

The fixture-backed Caret wrapper gate proves argv routing and process lifecycle,
not authenticated installed Claude/Codex/Gemini/Kimi execution. Keep
`caret-installed-provider-launches` TODO until the bounded real-provider
receipts exist.

Linked worktrees share the common Git hooks directory. Install only the stable
`scripts/hooks/pre-push-worktree-launcher`, which resolves the active worktree
and enters its tracked dispatcher. Never install an absolute symlink to one
worktree's dispatcher, and never preserve a legacy dispatcher as
`pre-push.local` because that creates recursive dispatch.

## 2026-08-21 bootstrap repair handoff

The must-check producer remains correctly blocked until a fresh Stage 4 exists.
The latest receipt-bound Stage 3 completed all 954 streaming surfaces, proving
the transient type-pool owner repair, but HIR then failed first on an aliased
ASM signature dependency. Do not promote compiler rows from partial Stage 3
logs. Resume from
`doc/08_tracking/bug/stage3_callable_dependency_named_glob_precedence_2026-08-21.md`:
named dependency routes now outrank overlapping globs while same-precedence
conflicts still fail closed. Only after Stage 4 and essential-tool smoke pass
may `check-bootstrap-must-pass.shs` update the source-bound ledger.

## 2026-09-06 local CI receipt: the `ci` tier and receipt admission

The manifest gained a third tier, `ci`, and two columns. The schema line is now
`must_check_gates |id, tier, push_blocking, mode, command, ci_job, inputs, description|`.
`ci_job` names the CI job allowed to skip that row; `inputs` is the path set the
`escalate` mode intersects against a rebase diff, with `*` meaning unbounded.
An unbounded row always re-runs — unknown escalates to running, never to
skipping. 27 rows carry `tier=ci` with `ci_job=code-idiom-gates`. Any parser you
touch must move with the columns: `validate_ledger_text()`'s awk,
`src/app/sj/gate_manifest.spl`, and `test/01_unit/scripts/must_check_tiering_test.shs`
change together, and `sh scripts/check/check-guard-wiring.shs` must stay green —
a row without a byte-matching dispatch case hits the fail-closed `*)` arm and
blocks every push.

The receipt is a SEPARATE document, `simple.local-ci-receipt/v1`, not ledger v4.
It references the manifest by `manifest_sha` and is signed with sshsig
(`ssh-keygen -Y sign|verify`, namespace `simple-ci-receipt`). Do not fold it into
`simple.must-check-ledger/v3`: the ledger is tracked, so a per-PR receipt written
into the tree it attests is circular; it would make every PR touch
`doc/08_tracking/check/`, serialising 8 concurrent sessions on one file; and the
two carry different trust classes. What IS reused is the manifest-parse and
id-set half of `validate_ledger_text()` — do not write a second parser.

Trust class, state it rather than implying more: a dev-key signature proves WHO
produced a receipt, not THAT the gates ran. Same class as
`review-admission.yml`'s `self_attestation`, whose own description says "this is
not independent authentication". There is deliberately no
`producer_id != reviewer_key_id` independence check, because a local receipt is
self-attestation by construction and a field that always holds trivially would
misrepresent the ceiling.

`config/check/ci_receipt_allowed_signers` ships with ZERO keys. That is the
fail-closed default, and `verify-local-ci-receipt.shs` selftest case c2 fails if
the shipped file ever admits a signer. The allowlist, the verifier and the skip
logic are read from the BASE ref, never the PR head, and a PR touching
`.github/workflows/`, `scripts/check/`, `scripts/hooks/` or `config/check/` is
refused admission outright — a receipt may never admit its own rules, so the PR
that adds a key always runs `full` itself.

Identity is TWO KINDS and both are supported. The receipt carries
`identities: <n>` then `identity: <kind> <value>` lines, kind in
`{change, patch}`, deduplicated and sorted ascending on the whole
`"<kind> <value>"` string: the jj `change-id` header when present, else
`git show <sha> | git patch-id --stable` for non-merge commits, else unbindable
with no third fallback. The kind is part of the SIGNED bytes, so a `patch`
identity never satisfies a `change` identity and a kind mismatch has its own
verdict — deliberate, because interchangeable kinds would be a forgery surface.
The fallback is load-bearing, not a nicety: measured 2026-09-06, 0 of the last
40 origin/main commits and 0 of PR #380's head commits carry a change-id header,
so without it the feature would never engage on a real PR. Verified end to end
on `c70a818a0` (no change-id header): sign exit 0 binding
`patch a251811056b6100759aab75b4863154ba3d3ad3f`, verify exit 0, tamper exit 1.
Selftests verifier 25/25, signer 18/18.

Delivery is a git note on `refs/notes/ci-receipts` keyed by the PR HEAD SHA (not
the tree, as design D2 first proposed) — it cannot be a tracked file, because
committing the receipt changes the tree it binds. **The signer has no
note-emission flag** (`git notes` and `--note` occur zero times in it), so the
producer runs `cat <receipt> <receipt>.sig > /tmp/note`,
`git notes --ref=ci-receipts add -f -F /tmp/note <head-sha>`,
`git push origin refs/notes/ci-receipts` by hand. That is the top usability gap.
The whole fast path is LOCAL-ONLY so far — it has never been exercised on a CI
runner; do not describe it as runner-proven. Also note the workflow emits FOUR
modes (`docs` was added alongside `sanity`/`escalate`/`full`) while its own
header comment still says three. Operator guide, with the full verdict-string
troubleshooting table: `doc/07_guide/infra/local_ci_receipt/operator_guide.md`.
## 2026-09-06 push dispatcher and guard-wiring landmines

- **The push consumer must take its dispatcher from the pushed ref, not the
  live checkout — the same invariant as the evidence hash above.** Until
  `3dfc6eb9202`, `check-push-must-pass.shs` read the gate manifest from the
  commit being pushed but matched rows against the dispatch arms of the
  WORKING-TREE copy of itself. On any manifest/dispatcher drift the fail-closed
  `*)` arm returned 2 while printing nothing, so the push died with "one or more
  manifest-declared push gates failed" although no blocking gate had failed.
  Now `*)` names the refused row and `load_committed_dispatcher()`
  (`check-push-must-pass.shs:393`, called at `:519`) redefines the dispatcher
  from the pushed commit's own copy. If a push fails with no gate named, suspect
  a stale dispatcher before suspecting a gate.
- **`sed -i` without a suffix never runs on macOS.** BSD sed consumes the script
  as the backup suffix and then parses the file path as a script.
  `check-runtime-source-list-parity.shs` had never executed on macOS for that
  reason; with its selftest green the real scan was red on every OS and the
  baseline was updated with traced provenance (`9838339c6cc`). Portable form,
  used at `:295`/`:315`: `sed ... "$f" > "$f.tmp" && mv "$f.tmp" "$f"`. Never
  `sed -i ''` — that breaks GNU sed.
- **Guard-wiring reachability counts mentions in COMMENTS.** Wiring guard A can
  make guard B, named only in A's header comment, newly "reachable" and turn
  B's row in `scripts/check/guard_wiring_unwired_baseline.txt` stale. Expect
  the cascade and fix B's row in the same change.
- **Binary-dependent guards belong in `rust-bootstrap-multiplatform.yml`**, the
  only workflow that builds the seed; `repo-hygiene.yml` has no binary and runs
  only `--selftest` (e.g. `check-ui-slim-closure.shs` at `repo-hygiene.yml:101`
  vs the real `--seed src/compiler_rust/target/bootstrap/simple` run at
  `rust-bootstrap-multiplatform.yml:201`; `check-ui-layout-branch-coverage.shs`
  at `:232`).
- **Stale-snapshot merge `e274cd33719`** ("merge all share-history worktree
  branches into main") deleted live, still-referenced code across many lanes.
  Before debugging any inexplicable "symbol not found", run
  `git show e274cd33719^:<file>` and diff.
