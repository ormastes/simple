# Windows Docker process provider test plan

Status: NOT_RUN. The parent's compiler repair budget is exhausted and no live
Windows fixture is attached. Do not substitute the Rust seed.

1. Validate explicit endpoint, executable, engine/boot/generation and finite bounds.
2. Reject mutable images, non-Windows metadata and mismatched versions.
3. Assert exact argv and explicit process isolation, ContainerUser and limits.
4. Reject actual isolation, image, owner or request mismatches before mutation.
5. Retain ambiguity on create timeout and reject duplicate retries.
6. Recover only a full exact ID matching the original request and all labels.
7. Preserve state on command failure and reject unknown IDs and unknown absence.
8. On a real Windows fixture: run chosen nonzero exit, bounded logs, stop/destroy,
   restart recovery, engine replacement, forbidden-mode and ownership negatives.
9. Run admitted SPipe/docgen/sspec-maintain and inspect the generated manual.

Live criteria additionally require Docker/Windows versions, exact image digest,
host/image compatibility, observed process isolation, no utility VM, timing/RSS,
ordinary-client policy and retained artifact provenance. Synthetic scripts do not
substitute for any live criterion.

The additional common API service scenarios cover initial quarantine, exact
scripted inventory refresh after journal ownership, unavailable inventory, wrong
acknowledgment and candidate recovery-only promotion. Protected workspace cases
cover policy/request versioning, literal mount argv, path escape and delimiter
rejection, zero/one mount inspection and actual selected-user mismatch. The
pinned remote producer's same-container workspace preflight and signed receipt
remain end-to-end integration criteria. All new Simple cases are NOT_RUN.
