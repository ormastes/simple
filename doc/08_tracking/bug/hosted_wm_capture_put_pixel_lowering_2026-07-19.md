# Hosted WM Capture `put_pixel` Lowering Failure

## Status

Open; blocks retained hosted framebuffer evidence for the Aetheric WM theme.

## Reproduction

```sh
sh scripts/check/check-hosted-wm-capture-evidence.shs
```

Using `bin/release/aarch64-apple-darwin-macho/simple`, the canonical checker
fails before rendering:

```text
HIR lowering error: Unknown variable: width while lowering HostedCaptureFramebuffer.put_pixel
error[E1002]: function `put_pixel` not found
hosted_wm_capture_reason=capture-program-failed
```

## Expected

The self-hosted compiler resolves the framebuffer method and the checker
retains a nonblank canonical hosted WM capture.

## Scope Decision

This is a compiler/lowering prerequisite rather than a theme ownership bug.
The theme implementation must not substitute fixture, synthetic, or private
renderer evidence. Fix the owner-level lowering defect, then rerun the checker
once in a fresh verification session.
