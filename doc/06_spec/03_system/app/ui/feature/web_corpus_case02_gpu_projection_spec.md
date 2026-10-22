# Web corpus case02 GPU DrawIR v4 projection

The executable source is `test/03_system/app/ui/feature/web_corpus_case02_gpu_projection_spec.spl`.

## Scenario: project the pinned six-command Web source

1. Read `test/fixtures/html_css/corpus/cases/02-fractional-edges.html` and authenticate SHA-256 `5ad0ddd4a7848160e220c116c7c7f21872a7f184d3444a2d97990e88da10bfe1`.
2. Run the real fractional Web producer through `web_corpus_case02_gpu_scene_from_html`.
3. Require CPU DrawIR v4 source, GPU DrawIR v4 output, one 640×480 unclipped GPU embedding, and source index map `[0, 1, 2, 3, 4, 5]`.
4. Require four opaque white full-surface integer rectangles followed by two opaque affine coverage rectangles. The latter retain viewport clips and have no source-only style or parent metadata in the GPU command.
5. Verify both recorded DrawIR digests by serializing the returned source and GPU compositions.

## Scenario: reject changed source

Changing the bar background from `#111` to `#222` must return `web-corpus-case02-html-sha256-mismatch` before GPU projection.

## Scenario: reject missing source paint metadata

Render the pinned source, remove `border-left-width` from the rotated tile's computed-style list, and call the projection helper directly. It must return `missing-source-paint-style:4:border-left-width` without building a GPU scene.

The adapter is a GPU DrawIR candidate. These scenarios do not assert native Vulkan execution or pixel parity. Runtime status remains unverified until the Simple test runner is available.
