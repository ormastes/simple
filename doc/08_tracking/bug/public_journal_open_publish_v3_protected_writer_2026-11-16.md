# Public Linux journal open/publish v3 is a broad protected-root writer

- Date: 2026-11-16
- Status: OPEN. Recorded only, no fix. It needs its own design review.
- Found by: signing lane step 3 (`facade/DECISION.md`, "Residual risks"). Re-verified at step 4 by reading source at `origin/release/1.0.0` `624843beeff`.
- Execution: NOT_RUN. No runnable `simple` binary on the host; every fact below comes from reading the source.

## Finding

Any caller can do the following with two public entries in `src/lib/common/task_runner/distributed_operation_journal_v2.spl`:

- `distributed_operation_journal_open_linux_v3` at `:693`
- `distributed_operation_journal_publish_v3` at `:623`

**1. It can create a protected root, not just open one.**
- `open_linux_v3` takes a caller-chosen `root: text` and calls `operation_health_linux_open_v1(root, binding)` (`:704`).
- That function defaults `writer = true` and `create_final = true` (`distributed_operation_owner_health_v2.spl:251-252`).
- In `src/lib/nogc_sync_mut/io/linux_protected_storage_v1.spl:211-212`, `create_final` makes the open `mkdirat` a missing final root component with mode 0700.
- So the call can provision a new protected directory that nobody administered.

**2. It replaces `parent.lease` on that root.**
- `operation_open_linux_held_v3` (`:714`) does `store.replace("parent.lease", lease)` (`:582`).
- That is a durable compare/replace mutation. It fences any other journal owner on the same parent.

**3. It then allows arbitrary no-replace writes.**
- `publish_v3` accepts any `relative` path that passes `distributed_operation_journal_relative_v3` (`:631`).

**4. There is no authorization gate.**
- `open_linux_v3` admits on syntactic validity of `authority_digest` and `nonce` (`builder_digest_valid_v1`), plus `maximum_events` bounds.
- Its only runtime gates are `linux_machine_process_origin_check_v1` (`owner_health_v2:253`) and OS permissions on the path.
- No signed-enrollment, policy or capability check binds which roots a caller may create or write.

## Why it matters

- The installer NARROW_BLOCK (`milestone_0011_signing_step3/facade/DECISION.md`) rejected every owner-side facade, because each one would be a "reader + caller-chosen identity" writer.
- This existing public API is strictly broader than any of them: text root in, protected writer out.
- So the protected-storage restriction that the installer lane is held to is not actually closed for other callers.

## Not done here, on purpose

- No visibility change.
- No narrowing of `open_linux_v3`'s `create_final`.
- No new gate.
- Callers of `open_linux_v3` depend on the current semantics, and choosing a gate is an owner decision for the journal and signing owners.

## Suggested direction (owner decision)

- Default `create_final=false` for `open_linux_v3`, and give genuine first-use provisioning an explicit admin-only path.
- Or require a typed protected-root capability (for example `LinuxProtectedRootReaderV1` for the exact root) instead of `root: text`.
- Then add a source spec with adverse cases: a missing root is refused, and an unprovisioned root is never created.
