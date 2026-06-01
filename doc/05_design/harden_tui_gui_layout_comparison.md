# Harden TUI/GUI Layout Comparison Design

Status: selected scope. User approved Feature Option 3 and NFR Option C on 2026-06-01.

## Data Contracts

`ComparisonResult` in `screenshot_compare.spl`:

- `exact_match`: full-buffer equality over a valid viewport.
- `match_percentage`: threshold-based diagnostic percentage in basis points.
- `different_pixels`: threshold-exceeding pixel count, or a nonzero failure count for invalid dimensions.
- `max_channel_diff` and `total_channel_diff`: diagnostic drift.
- `passed`: policy result after exact/threshold profile evaluation.

`CaptureResult` in `html_compat`:

- `success` gates comparison before pixel inspection.
- `width` and `height` must equal the requested viewport.
- `pixels.len()` must equal `width * height`.
- `error` carries capture, metadata, or timeout diagnostics.

`SiteCorpusPair`:

- `chrome_ok` and `simple_ok` represent source validity separately.
- `exact` and `accepted` represent comparison result separately.
- perceptual percentage is diagnostic-only under the current exact acceptance policy.

## Algorithms

Exact pixel comparison:

1. Reject `width <= 0` or `height <= 0`.
2. Compute `expected = width * height`.
3. Reject either buffer whose length differs from `expected`.
4. Compare every pixel and every channel.
5. Report exact equality separately from threshold pass semantics.

Perceptual comparison:

1. Reject invalid dimensions.
2. Reject incomplete buffers.
3. Score full-viewport pixels only.
4. Do not set acceptance directly.

Pair comparison:

1. Preserve failed Chrome/Simple capture diagnostics.
2. Reject Chrome metadata mismatch.
3. Reject Simple metadata mismatch.
4. Run exact comparison.
5. If exact fails, compute perceptual diagnostics and write exact-only policy into reports.

Diff image generation:

1. Reject invalid dimensions with an empty diagnostic image.
2. Produce exactly `width * height` pixels for valid dimensions.
3. Mark identical pixels green and missing/different pixels red.

Backend probing:

1. Probe Metal, Vulkan, CUDA, ROCm/OpenCL, and CPU SIMD lanes explicitly.
2. Select the best initialized backend in deterministic priority order.
3. Include per-lane status fields in the runtime evidence summary.
4. Treat unavailable and failed states as evidence, not as hidden fallback success.

## Test Surface

Current focused specs cover:

- invalid dimensions and truncated buffers for compositor comparison,
- diff-image completeness for truncated buffers,
- invalid/truncated exact and perceptual HTML comparison,
- pair-level viewport metadata mismatch,
- famous-site corpus pair metadata mismatch,
- backend runtime evidence fields for Metal, Vulkan, CUDA, and CPU SIMD lanes.

## Structural Layout Design

Add a structural comparison report type that can hold:

- source name,
- viewport,
- TUI cell rows/columns or GUI layout boxes,
- stable node labels,
- text line metrics,
- geometry mismatch list,
- pixel comparison link,
- backend evidence link.

The structural comparison path runs before pixel comparison. Its result should be attached to HTML/corpus reports and future TUI reports as diagnostic evidence. Pixel exactness remains the current acceptance gate until a later requirement explicitly accepts structural-only parity.

## Measurement Design

Add measurement records with:

- command,
- host,
- backend,
- warmup count,
- sample count,
- p50,
- p95,
- max RSS,
- render/readback scope,
- artifact size deltas.

Measurement records must be backend-qualified. A software fallback measurement can be useful baseline evidence, but it must not satisfy a Metal, Vulkan, CUDA, or CPU SIMD lane.
