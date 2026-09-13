# Draw IR window shadow is clipped and overwritten

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Observed

The canonical WM window batch emits a translucent shadow RECT at local `(5,6)`
with the full window size, then a full-window body RECT. The embedded surface is
exactly the window size and clipped, so the body overwrites every in-bounds
shadow pixel and the displaced right/bottom pixels never leave the child.

## Owner fix

Keep the fix in the canonical WM Draw IR producer: represent the shadow with
bounds that survive the embedded-surface clip (or a separate ordered surface),
without adding a GUI-specific renderer path. Preserve hit/layout bounds and
verify identical local CPU and checked host-device output.

## Acceptance

- A pixel outside the window body but inside the declared shadow is visible.
- Window/body/content hit and clip bounds remain unchanged.
- CPU and checked Vulkan composition remain exact for focused and unfocused windows.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
