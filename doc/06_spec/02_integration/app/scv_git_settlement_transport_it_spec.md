# Git settlement read-back transport

Source: `test/02_integration/app/scv_git_settlement_transport_it_spec.spl`.

This manual is authored pending SPipe generation. The scenarios have **not** been executed with an admitted pure-Simple runtime. They exercise the production read-only Git transport against isolated real local repositories; they do not prove GitHub protected-ref capabilities, worker identity, receipt admission, or publication.

## Reconcile a lost acknowledgement from the actual authority ref

Requirements: REQ-008, REQ-022.

1. Prepare a bare local Git authority at `refs/heads/settled` and a candidate whose sole parent is the genesis head.
2. Call `db_git_settlement_reconcile` before publication. Capture `not_published` and the genesis head from `db_git_settlement_ref_head`.
3. Publish the candidate with real Git, call production reconciliation again, and capture `published` with the exact candidate OID.

## Hold allocation when canonical history moves beyond an uncertain candidate

Requirement: REQ-008.

1. Publish the candidate and then a descendant commit to the isolated authority.
2. Reconcile the original candidate. Capture `SCVDB_HISTORY_REQUIRED` and the later head OID. This status forbids allocation until canonical ancestry and receipt history are verified by a higher layer.

## Reject a wrong parent and unsafe or unavailable remote

Requirements: REQ-008, REQ-022, NFR-013.

1. Supply a candidate with the wrong expected parent and then a malformed old OID. Capture `SCVDB_PARENT_MISMATCH` and `SCVDB_GIT_OID` before remote read-back.
2. Supply credential-bearing, extra-path, and control-character GitHub HTTPS URLs. Capture `SCVDB_REMOTE_SCOPE`; the token is never passed to Git or returned.
3. Delete the fixture authority ref. Capture `SCVDB_READBACK_UNAVAILABLE` from both head and reconciliation APIs.

## Reject local replacement-ref parent forgery

Requirements: REQ-008, NFR-010.

1. Publish a candidate and its child to the isolated authority.
2. Install a local `git replace --graft` ref that makes a revision walk falsely report the second commit as a direct child of genesis.
3. Call production reconciliation for that false parent and capture `SCVDB_PARENT_MISMATCH`. Production reads the raw commit object with replacement disabled.

The transport accepts only absolute local repositories or credential-free `https://github.com/<owner>/<repository>` URLs, with an optional `.git` repository suffix. Git authentication for the latter comes from the trusted process environment. The adapter returns classified status only and never propagates Git stderr. A live GitHub authority still requires independent protection, restricted worker identity, semantic receipt verification, and a publication implementation before allocator admission.
