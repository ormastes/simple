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
