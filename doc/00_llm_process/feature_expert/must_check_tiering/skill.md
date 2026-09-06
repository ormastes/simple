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

Two gaps are open and must not be papered over. **Delivery:** design D2 puts the
receipt in a git note under `refs/notes/ci-receipts` keyed by the TREE object;
the landed scripts and `repo-hygiene.yml` instead read the tracked path
`doc/08_tracking/check/local_ci_receipt.v1.txt`, and `git notes` appears nowhere
in them. Committing the receipt re-creates the §3.1 circularity, so no PR can
deliver one today. **Identity:** `decide()` resolves change-id header, else
`git patch-id --stable` for non-merge commits, else unbindable; but
`verify-local-ci-receipt.shs` reads change-id headers only and has no fallback by
design. Measured 2026-09-06, 0 of the last 40 origin/main commits and 0 of PR
#380's head commits carry a change-id header, so every real PR resolves as
patch-id and is refused into `full`. Operator guide, with the full verdict-string
troubleshooting table: `doc/07_guide/infra/local_ci_receipt/operator_guide.md`.
