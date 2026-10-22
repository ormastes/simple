# Corpus case 02 analytic pixel oracle

Manual companion to
`test/01_unit/lib/common/renderdoc/corpus_case02_polygon_oracle_spec.spl`.
The independent oracle module is
`src/lib/common/renderdoc/corpus_case02_polygon_oracle.spl` and its
predeclared policy is
`test/fixtures/html_css/corpus/oracles/02-fractional-edges.oracle.json`.
Generated SPipe output awaits a trustworthy Simple runner.

## Authored scene and pixel domain

The source is the pinned 640 × 480 case 02 HTML file with SHA-256
`5ad0ddd4a7848160e220c116c7c7f21872a7f184d3444a2d97990e88da10bfe1`.
The page and `#scene` paint opaque white. The tile is local
`(0,0,180.5,100)`, fill `#247bde`, rotated seven degrees about its center
after the authored quarter-pixel translation. The separate `#111` bar covers
the half-open rectangle `[290.5,293) × [40.25,320.75)`.

The oracle intersects the transformed tile polygon and bar rectangle with
each pixel square. Coverage is opaque SrcOver in encoded sRGB channels over
white, rounded to the nearest byte with halves up. Output is tightly packed
top-left straight RGBA8 with sRGB primaries and transfer; every alpha is 255.
The exact oracle digest is
`8b59b0b26ab92d1a436639b9b65c1ab28388f4871c3b05890eae982189884d4d`.

## Frozen comparison policy

Coverage within `1e-12` of zero or one snaps to that endpoint. Pixels with
coverage zero or one require exact RGBA. Every other pixel is an edge pixel:
alpha must equal 255, each RGB channel may differ by at most 16, and the
mean absolute RGB channel difference across all edge pixels may not exceed 4.
No edge pixel may exceed its per-channel limit. The policy was pinned before
device output. There are 17,730 tile interior pixels, 558 bar interior pixels,
287,998 exterior pixels, 629 tile edge pixels, and 285 bar edge pixels.

Backend readbacks reported as sRGB premultiplied surfaces require completed
resource selection and conversion to canonical straight RGBA8 before this
comparison. Since the authored output is opaque, the adapter must verify
every final alpha is 255 before labeling the canonical result `opaque`.
Unconverted premultiplied metadata is rejected by the final-output decoder.

## Assertions and evidence limit

The focused spec checks the pinned source and oracle digest, all five region
counts, exact white/tile/bar probes, and two analytic edge probes. It shows
ideal pixels pass, wrong interior and exterior pixels fail, an eight-level
edge change passes, a seventeen-level change fails, and a global five-level
edge error fails the aggregate bound. A synthetic completed capture proves
the canonical adapter path and source-digest binding without claiming a GPU
capture.

The analytic oracle is an independent ideal coverage target. It is not a
Chromium screenshot or a captured Vulkan golden. Case 02 remains `not-run`
for Vulkan parity until physical captures from both backends include trusted
resource, completion, device UUID, and color-domain receipts.

Requirements: REQ-2D-003, REQ-2D-004, REQ-2D-006, NFR-2D-003,
NFR-2D-004.
