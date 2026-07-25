# NFR Options: Simple WM Modernization

Date: 2026-06-02

## Option A: Lightweight Motion Budget

Pros:
- Keeps animation CSS-only and avoids request-handler work.
- Easy to disable with reduced-motion media query.

Cons:
- Does not prove smoothness on low-end devices without browser measurement.

Effort: Low.

## Option B: Visual Quality Gate

Pros:
- Adds objective checks for contrast, overlap, text clipping, and screenshot stability.
- Good fit for GUI quality expectations in the request.

Cons:
- Baselines can be noisy across hosts unless tightly scoped.

Effort: Medium.

## Option C: Cross-Backend Parity Gate

Pros:
- Proves web/native/QEMU shell consistency.
- Aligns with SimpleOS desktop ambitions.

Cons:
- Slowest and most brittle gate; requires broad infrastructure.

Effort: High.
