<!-- codex-research -->
# Showcase apps — domain research

A renderer showcase is both a demonstration and a conformance fixture. It should use deterministic content, group features by capability, expose interaction state, and distinguish unsupported behavior from successful blank output.

The web page therefore groups semantic text, lists, tables, forms, flex/grid, positioning, overflow, responsive CSS, and advanced probes. The 2D app should group primitives, transforms, clipping, alpha/blending, images, text, paths, and readback. Every hosted surface must preserve the same app identity and behavior rather than substitute a platform-specific mock.

Verification needs semantic state plus pixels: visible labels and control state, routed pointer/keyboard events, nonblank frame/readback, stable dimensions/checksum, and explicit backend provenance. QEMU evidence must come from an installed SimpleOS app and guest WM window, not a host wrapper or fixed transcript.
