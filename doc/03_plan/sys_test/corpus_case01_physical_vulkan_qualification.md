# Corpus case 01 physical Vulkan qualification

REQ-2D-006 and NFR-2D-002 require the actual 48-case Web source path to
reach both backends. Case `01-solid-boxes` is the first bounded corpus scene.
Its source HTML SHA-256 is
`2386d4aa5219ba762839a3897fa18d8775991243706668775bd8771a722737d2`;
the independent SVG reference SHA-256 is
`6f644ae156fec78dfecd7e50e7b5c5f0c59b8396bcd2dd6063a1227b6838ec31`.
The viewport is 640 × 480 at DPR 1. The independent oracle has a white
canvas and red, blue, and green authored rectangles; its 1,228,800 RGBA
bytes hash to
`2f4d3fb17e0a1ab65cba1f3b3950f1cf67b51f2f09df5faac247c2dc858039e9`.

## Admission and execution

The Web producer must render the pinned HTML and retain the original DrawIR
hash and source-command indexes. GPU commands must use the producer's
resolved geometry, colors, and paint order. The admission checks every
command's source-node identity, parent, clip, opaque color, style, and
payload. The `#scene` overflow clip is redundant only if its actual
untransformed rectangle and all emitted clips cover the full 640 × 480
target. Any narrower clip or unsupported effect fails closed. The three
colored divs have anonymous producer-generated IDs; the admission validates
them against the actual DOM rather than inventing new IDs.

The physical runner must carry a scene descriptor through both isolated
workers and receipt verification. Its case 01 capture has width 640,
height 480, stride 2560, and exactly 1,228,800 canonical RGBA bytes.
Engine2D and upstream Skia must consume the same admitted GPU DrawIR, submit
on a physical Linux Vulkan device, finish readback, record source and GPU
digests, and agree on physical-device and driver UUIDs. Each pixel must
equal the independent oracle. A retained receipt inspected offline remains
a candidate; it cannot prove a fresh physical run.

On a physical Linux Vulkan host, use a qualified compiled worker and the
authenticated upstream Skia provider:

```text
sh scripts/check/check-vulkan-2d-qualification.shs <absolute-qualified-executable> <absolute-skia-provider> build/test-artifacts/vulkan_2d/<fresh-id> corpus-case01
```

## Current evidence

The pinned source/reference hashes, independent oracle bytes, Web admission
entrypoint, scene-descriptor workers, and candidate verifier are available.
The expected seven-command Web producer inventory has not been observed by a
trustworthy Simple runtime. No Simple spec or physical Linux GPU execution
has passed for this case. Other corpus cases remain separate qualifications.

Astra's source review found no definite false admission or guaranteed false
rejection in the current case 01 path. CSS alone cannot prove that Web layout
emits full-target clips, so the runtime admission must observe and check all
seven commands and their actual clips before either backend runs. Keep the
fail-closed inventory and style checks until a trustworthy producer result
shows what needs to change.
