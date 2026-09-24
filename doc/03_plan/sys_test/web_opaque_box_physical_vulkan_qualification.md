# Physical Vulkan Web opaque-box qualification (REQ-2D-006 / NFR-2D-002)

The input is the pinned `web_opaque_box_v1.html` fixture. Each native worker
reads it as a regular file without following a symlink, checks its SHA-256,
and calls `web_opaque_box_gpu_scene_from_html`. Admission requires the real
Web layout result with no degraded render, fallback material, or unproved
paint state. The worker submits that call's GPU DrawIR value directly.

Run on a Linux host with a physical integrated or discrete Vulkan device,
the pinned qualification executable, and the authenticated upstream Skia
Ganesh Vulkan provider:

```text
<qualified-executable> run-web-box <absolute-qualified-executable> <absolute-skia-provider> build/test-artifacts/vulkan_2d/<fresh-id>
```

Engine2D and Skia run in separate native processes. Their candidate receipts
record the HTML fixture SHA-256, a viewport/DPR/input-state digest, original
Web DrawIR SHA-256, admitted GPU
DrawIR SHA-256, source and GPU command counts, and source-command indexes.
The verifier independently recomputes the Web projection and requires those
fields to match both receipts. It also requires completed device readbacks,
the same physical-device and driver UUIDs, exact equality between the two
1024-byte frames, and the independent 16 × 16 opaque-box pixel oracle.

`verify-web-box` can inspect retained receipts, but reports only a candidate.
The focused system spec exercises admission and negative capture boundaries;
constructed frames are not physical evidence. No physical Linux GPU PASS was
observed on the macOS development host.
