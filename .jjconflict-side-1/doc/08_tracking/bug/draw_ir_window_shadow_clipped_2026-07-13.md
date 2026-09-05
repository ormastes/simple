# Draw IR window shadow is clipped and overwritten

Status: open (TODO 554)

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
