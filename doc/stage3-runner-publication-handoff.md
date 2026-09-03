# Stage 3 runner publication / descriptor handoff

Status: **publication slice complete; capsule verifier integration remains a
separate merge lane**. This isolated slice was not applied to an authoritative
lane. No Stage 3, bootstrap, Git operation, service, or heavy build ran.

## Frozen work

- `bootstrap-stage3-shared-runner.pl` now descriptor-walks canonical file
  parents with `openat(O_NOFOLLOW)`, retains opened evidence identities, and
  passes direct evidence to the provenance verifier and analyzer by
  `/proc/<runner>/fd/<n>` references.
- Final runner PASS bytes are fsynced in an anonymous `O_TMPFILE` inode. Named
  prepared and commit records are durable and explicitly `status=prepared`.
  A no-replace `linkat` to `runner-receipt.env` is the last operation before
  `_exit`.
- Candidate provenance-verification PASS uses the same production helper and
  separate `.candidate-provenance-verification.{prepared,commit}.<run-id>`
  records. Its verifier capture is anonymous; after the no-replace canonical
  link, the analyzer consumes the retained PASS descriptor instead of reopening
  `candidate-provenance-verification.env`.
- Result files are opened, hashed, fsynced, parent-fsynced, and retained in one
  descriptor walk. Candidate, provenance, transcript, raw, memory, and phase
  inputs are not closed and reopened between durability and use.
- `bootstrap-stage3-provenance-verifier.shs` has descriptor-only primary input
  validation plus canonical display-path companions.
- `bootstrap_stage3_runner_publication_contract_test.shs` extracts and invokes
  the exact production publication/recovery helper definitions; mutation
  orchestration exists only in the generated test harness, with no production
  self-test CLI. It covers real file and parent `sync` failures, real cleanup
  `unlink` failures, prepared/commit/final link collisions, pre-link and
  post-link crashes, directory replacement before/after preparation, incumbent
  preservation, canonical/prepared byte and inode tampering, and commit byte or
  extra-blank-line tampering. The durable commit is the recovery trust root by
  exact ordered content; no separate record claims to bind its inode identity.

Pre-review focused publication mutation result: PASS in 7.30 seconds, 11,520
KiB maximum RSS. Focused shared-runner result: PASS in 1.37 seconds, 21,248 KiB
maximum RSS on its third and final cycle; the first two failures were missing
synthetic helper-tree fixture setup only. The post-review hardening removed the
production mutation CLI, made console/marker creation descriptor-relative, and
tightened recovery/tamper assertions. Per the three-cycle cap, those green
checks were not rerun in this slice; the combined parent integration gate owns
the next execution.

## Storage-crash contract

The protocol proves process-crash recovery: acceptance requires the exact
canonical inode/hash and its durable prepared/commit identity chain. The
canonical link is intentionally the last filesystem operation, so no directory
fsync follows it. After a storage crash, the canonical directory entry may be
lost while the durable non-PASS commit remains. Commit alone is never success;
recovery must run verification again. The focused test rejects commit-only
recovery for both receipt kinds.

## Separate capsule merge requirements

The capsule-verifier lane must provide the held Stage 3 transcript descriptor
and display equality audit, strict canonical `/proc/<pid>/fd/<fd>` grammar, and
a complete retained descriptor bundle for analyzer/runner/resume/shell plus
plan-derived candidate and identity inputs. Display paths are audit strings
only; that lane must not reopen them or mutable ancestors. Its independent
xhigh acceptance is required before authoritative integration.
