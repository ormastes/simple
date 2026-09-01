# Must-check external receipts are self-attested

Status: implementation and focused review PASS; production reviewer key TODO;
not pushed

## Failure

`check-bootstrap-must-pass.shs --record-gate-pass` verifies that a receipt and
its artifact are committed, hash-bound, source-bound, and labelled `PASS`.
Except for `stage4-tooling-matrix`, it does not interpret the artifact or invoke
a registry-owned validator. A schema-correct receipt can therefore promote an
external GPU, server, board, toolchain, or benchmark TODO while its artifact is
arbitrary text.

The focused baseline reproduces this at current `dcc1e68294`: the fixture
artifact contains only `fixture manual gate artifact`, yet
`test/01_unit/scripts/must_check_tiering_test.shs` records the manual row as
PASS. The complete focused test exits 0 in 10 seconds, proving that this weak
acceptance is the intended current behavior rather than a malformed fixture.

## Required fix

- External evidence rows name a validator in the committed registry.
- Recording runs that validator only in the bootstrap-owned recorder, against
  exact committed receipt and artifact blobs.
- Exit zero is insufficient: the validator's final non-empty line must be an
  accepted PASS verdict.
- Unknown, missing, failing, or incidental-PASS validators fail closed without
  changing the ledger.
- The interactive push consumer continues to perform bounded exact-ref hashing
  and never executes external validators.
- Focused fixtures cover a semantic rejection and an accepted validated
  artifact while retaining the existing hash, source, replay, and downgrade
  checks.

## Attempt evidence and remaining blocker

On 2026-08-24, `sh test/01_unit/scripts/must_check_tiering_test.shs` passed
after rejecting independent-review, incomplete-count, and missing-acceptance
mutations. The exact pushed-ref path remained one second; external validation
was not added to that hot path. Shell syntax, `git diff --check`, the
generated-spec layout guard (`0` misplaced `.spl` files), and the working-tree
direct-env/runtime guard also passed.

High-capability review then rejected the implementation: the candidate
validator checks only that artifact-supplied digests are nonzero hex and that
artifact-supplied acceptance IDs/counts have the expected shape. It does not
recompute those digests from separately retained blobs or verify a reviewer
signature/attestation. A hand-written schema-shaped artifact can therefore
still self-attest. The next cycle must add committed evidence references,
recompute every binding, and verify a repository-pinned reviewer authority (or
adopt another equally falsifiable authority boundary) before any promotion.

The v2 candidate now references four separate committed blobs (command,
target, toolchain, and observations), recomputes each hash from `HEAD`, checks
shared gate/source/run identity, and verifies every gate-specific acceptance
marker. Its summary requires an OpenSSL SHA-256 signature from a public key
pinned by repository path and hash. The production policy is empty until a real
independent-review key is provisioned, so missing authority stays blocked rather
than falling back to self-attestation. External PASS also resets on a changed
source fingerprint; stale signed evidence is not carried forward. Fixture trust
is exercised by copying the validator into a separate committed test repository,
not through a production key/policy override. Fresh focused verification and
final review are pending.

The recorder independently binds manifest and ledger paths to the same physical
root and rejects symlinks. This prevents self-test phase/runner overrides in a
disposable repository from writing PASS rows into the production ledger.

Cycle-three review found one remaining fail-closed defect. The observation
validator counts only `acceptance.<id>=PASS` lines. A blob containing both
`acceptance.no-leak=PASS` and `acceptance.no-leak=FAIL` still satisfies the PASS
count because the contradictory line is ignored. The next cycle must reject
every `acceptance.*` line outside the exact expected PASS set and add explicit
PASS+FAIL and PASS+BLOCKED mutation fixtures. No v2 change is committed or
pushed until that review passes.

The follow-up candidate now compares the count of every `acceptance.*` line to
the exact required set as well as validating each required PASS marker. Any
extra FAIL, BLOCKED, unknown, duplicate, or malformed acceptance line therefore
fails closed. The focused fixture signs internally hash-consistent summaries
containing PASS+FAIL and PASS+BLOCKED contradictions so those mutations reach
the observation oracle rather than failing earlier at the hash/signature layer.

The focused contract passed after this change, with the exact pushed-ref path
remaining below one second in the retained measurement. High-capability review
accepted the code/trust boundaries. Production external promotion remains
honestly unavailable until an independent reviewer public key is provisioned
in `config/check/must_check_external_reviewers.sdn`; the empty policy is a
fail-closed prerequisite, not a fallback to self-attestation.
