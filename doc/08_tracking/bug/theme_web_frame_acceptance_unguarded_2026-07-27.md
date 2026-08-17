# Bug: external Web frame acceptance never reads or stores a theme identity at all — not just stale after a theme change

**Date:** 2026-07-27
**Status:** open
**Found:** side-finding while agents worked on other tasks, 2026-07-27
**Area:** OS compositor (`src/os/compositor/host_compositor_core.spl`) — external Web content-frame authorization
**Severity:** High — a fail-closed gate that isn't closing; every externally-supplied frame is unguarded, not merely frames arriving after a theme change

## Finding

`HostCompositor.set_external_web_frame` — the function that authorizes and
stores an externally-supplied Web content frame
(`src/os/compositor/host_compositor_core.spl:650-666`) — validates window id,
origin kind, dimensions, pixel-buffer length, checksum, parent/offset
constraints, and `wm_content_frame_web_provenance_valid(frame)`, but never
reads the active theme and never stores a theme key at registration:

```
me set_external_web_frame(
    window_id: i64,
    frame: WmContentFrame
) -> bool:
    if (not self.external_web_required or
        window_id != self.external_web_window_id or
        frame.window_id != window_id.to_text() or
        frame.origin_kind != WM_CONTENT_ORIGIN_SIMPLE_WEB or
        frame.width <= 0 or frame.height <= 0 or
        frame.width > 4096 or frame.height > 4096 or
        frame.pixels.len() !=
            frame.width.to_i64() * frame.height.to_i64() or
        frame.checksum == 0u64 or
        frame.checksum != wm_content_frame_checksum(frame.pixels) or
        frame.parent_window_id != "" or
        frame.offset_x != 0 or frame.offset_y != 0 or
        not wm_content_frame_web_provenance_valid(frame)):
        return false
    self.external_web_frame = frame
    self.dirty.add_full_screen(self.width, self.height)
    true
```

`require_external_web_frame` (lines 644-648), the companion registration
function called before frames start arriving, also never touches theme
state — it only sets `external_web_required`/`external_web_window_id` and
resets `external_web_frame` to an empty sentinel.

`WmContentFrame` does carry theme-provenance fields elsewhere in this same
file — e.g. the debug print statements at lines 1059 and 1101 reference
`frame.theme_id` and `frame.theme_source_manifest_sha256` — so the type
supports a theme identity, but `set_external_web_frame` simply does not
check it. This is a stronger defect than
`doc/08_tracking/bug/theme_snapshot_catalog_review_hard_stop_2026-07-27.md`
documents: that doc's P1 gap #2 describes a frame/registration theme key that
is stored at registration but not recompared after a later theme change. Here,
no theme key is stored **at registration at all** — the gate never engages,
for any frame, regardless of whether a theme change ever occurs.

### `host_wm_theme_bootstrap.spl` checks presence, not identity

`install_default_host_wm_theme`
(`src/os/compositor/host_wm_theme_bootstrap.spl:19-26`):

```
fn install_default_host_wm_theme() -> ThemeRenderSnapshot:
    # Preserve an explicit earlier selection. Fresh hosted launches resolve the
    # registry default package instead of bypassing it with a generated copy.
    if active_wm_theme_snapshot_present():
        val snapshot = active_wm_theme_snapshot_unchecked()
        apply_theme_render_snapshot_to_wm_chrome(snapshot)
        return snapshot
    install_host_wm_theme(default_theme_id())
```

confirms the claim: it only checks `active_wm_theme_snapshot_present()` (does
a snapshot exist at all) and, if so, reinstalls it via
`active_wm_theme_snapshot_unchecked()` without validating that snapshot's
identity against the registry/catalog default. This matches P1 gap #1 in the
hard-stop doc referenced above.

## Impact

`external_web_required`/checksum/provenance checks give the appearance of a
fail-closed content-authorization boundary, but the theme axis of that
boundary never engages. Any content frame that passes the existing
dimension/checksum/provenance checks is accepted regardless of what theme
(if any) was active when the window was registered vs. when the frame
arrives.

## Suggested fix

Do not patch this piecemeal — the parent hard-stop doc
(`doc/08_tracking/bug/theme_snapshot_catalog_review_hard_stop_2026-07-27.md`)
explicitly forbids incremental repair here after three rejected repair
cycles, and a real fix needs a product decision this doc cannot make alone:

1. **Fail-closed vs. reinstall-default policy** — should
   `install_default_host_wm_theme` (and `set_external_web_frame`) refuse to
   proceed when there is no verifiable active/catalog theme identity, or
   silently fall back to a known-safe default? The current code effectively
   does neither: it reinstalls whatever is present unchecked.
2. **Which identity axis is authoritative** — the hard-stop doc's resume
   contract (§ "Fresh-lane resume contract", items 1-2) calls for validating
   any existing active snapshot against the authoritative hosted
   registry/catalog identity, and comparing the frame/registration key
   against the *current* installed active theme at every acceptance (or
   invalidating all registrations atomically on theme change) — but the
   authoritative identity source (registry id? content hash? render-snapshot
   version?) is not yet decided, which is presumably why three prior repair
   attempts were rejected rather than landed piecemeal.

Any fix here should go through the same review gate the hard-stop doc
requires (item 6 of its resume contract: independent highest-capability
review before integration) rather than a local patch to
`set_external_web_frame` alone.

## Related

- `doc/08_tracking/bug/theme_snapshot_catalog_review_hard_stop_2026-07-27.md`
  — parent hard-stop doc; its P1 gap #2 documents the narrower staleness
  case (theme key stored but not recompared after a change). This doc
  documents the broader defect: no theme key is stored at registration at
  all.
- `src/os/compositor/host_compositor_core.spl:644-666` —
  `require_external_web_frame` / `set_external_web_frame`.
- `src/os/compositor/host_wm_theme_bootstrap.spl:19-26` —
  `install_default_host_wm_theme`, presence-only check.

---

## Fixed 2026-08-17 (worker W7)

Binary for every number below: `bin/release/x86_64-unknown-linux-gnu/simple`
(Rust seed, interpreter path). No bootstrap was run.

### Reproduced behaviourally first

`test/01_unit/os/compositor/external_web_frame_theme_identity_guard_spec.spl`
drives a real headless `HostCompositor`, registers a window, and offers a
correctly-checksummed frame stamped `theme_id: "attacker-theme-never-installed"`.

**Before: `Results: 4 total, 2 passed, 2 failed`.** The two failures are the
hostile theme id via `set_external_web_frame` and via
`set_external_web_frame_owned` — both ACCEPTED. Note which two PASSED: an empty
`theme_id` was already refused (by `wm_content_frame_web_provenance_valid`) and
the active theme was accepted. So the gate checked theme *presence* and never
theme *identity* — any non-empty string got in.

### Fix

`src/os/compositor/host_compositor_core.spl`: extracted
`_host_active_content_theme_id()` and used it on BOTH sides of the boundary —
the produce path (the content-revision loop, which already resolved
`active_wm_theme_id()` with a `default_theme_id()` fallback and now calls the
helper) and the accept path (`_set_external_web_frame_with_ownership`, one new
disjunct `frame.theme_id != _host_active_content_theme_id()`). Both public
doors (`set_external_web_frame`, `set_external_web_frame_owned`) funnel through
that single predicate, so there is no second entrance.

**After: `Results: 4 total, 4 passed, 0 failed`.**

### On the parent doc's "no piecemeal repair" hard stop

Item 2 of that resume contract asks which identity axis is authoritative. This
change does **not** decide that — it adopts, unchanged, the resolution this
same file already used when STAMPING `theme_id` onto produced frames
(`active_wm_theme_id()`, falling back to `default_theme_id()` when no theme is
installed). Accepting under a different rule than you produce under is the
inconsistency, not a policy choice. Extracting the helper makes the two sides
structurally incapable of drifting. The remaining open policy questions —
fail-closed vs. reinstall-default in `install_default_host_wm_theme`, and
atomic invalidation of registrations on theme change — are untouched and still
belong to the parent doc's review gate.

`host_wm_theme_bootstrap.spl`'s presence-only check (P1 gap #1) is **NOT**
addressed here; it is the part that genuinely needs the product decision.

### Regression check (ablation)

`hosted_external_web_frame_spec.spl` and `hosted_web_content_session_spec.spl`
both report `Results: 1 total, 0 passed, 1 failed` **with and without** this
change (verified by restoring the file from HEAD and re-running). Pre-existing
red, not introduced here.
