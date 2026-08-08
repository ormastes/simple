# Hosted Stop pointer retirement

> Deferred Stop activation preserves the committed page and retained resources,
> retires parent and worker press ownership, and rejects the old release before
> it can emit pointer-up or reach the click path.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 1 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Status | Implemented static; execution held |
| Source | `test/03_system/security/browser_stop_pointer_retirement_spec.spl` |
| Requirements | REQ-WEB-BROWSER-008, 009, 014, 018, 021 |
| Updated | 2026-07-30 |

## Scenario

### should reject a pre-Stop release without losing committed content

1. **Prime a completed content pointer press**
   - Commit a worker document and retain one parent-owned image resource.
   - Hold parent press/cancel ownership and worker content/chrome press state.
   - Leave an older navigation command partially written to select the
     deferred-Stop activation path.

2. **Dispatch Stop through the hosted parent**
   - Submit Stop and prove it waits for the partial write.
   - Complete the old write and invoke the real deferred activation.
   - Assert Stop is now pending and parent press/cancel state is retired.

3. **Acknowledge Stop in the renderer worker**
   - Decode the actual parent Stop wire and dispatch its navigation message.
   - Assert worker content/default-action/chrome press state is retired.
   - Assert the already committed URL and HTML remain visible.

4. **Reject the stale post-Stop release**
   - Assert the parent still owns its committed URL and retained image.
   - Submit the release belonging to the pre-Stop press.
   - Require `pointer-release-target-mismatch`, unchanged Stop wire, and an
     unchanged request sequence. No pointer-up reaches the worker, whose cleared
     pressed target also cannot synthesize a click.

The scenario is implemented but execution remains held until a source-matched
admitted pure-Simple full CLI is available. No seed or bootstrap evidence may
promote this manual.
