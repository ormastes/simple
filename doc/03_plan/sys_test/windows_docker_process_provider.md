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
