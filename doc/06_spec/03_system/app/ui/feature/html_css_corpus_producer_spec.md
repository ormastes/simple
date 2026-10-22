# Pinned HTML/CSS Web producer corpus

Executable source: `test/03_system/app/ui/feature/html_css_corpus_producer_spec.spl`

Trace: REQ-2D-006, NFR-2D-002

Run from the repository root with
`bin/release/aarch64-apple-darwin/simple test test/03_system/app/ui/feature/html_css_corpus_producer_spec.spl --mode=interpreter`.
This scenario has not been run in the current checkout. The focused GUI
scenario below hit a test-runner parse failure in unrelated
`src/lib/nogc_sync_mut/io/process_ops.spl`; no Web result is claimed here.

## Scenario: execute the 48 pinned pages

1. Parse `test/fixtures/html_css/corpus/manifest.json` and require 48 cases.
2. For each case, verify the source SHA-256 and 640 × 480 viewport, then call
   the existing Web HTML layout producer. Record the number of computed styles,
   layout boxes and DrawIR commands, and any layout degradation reason. Lower
   each composition through the shared `draw_ir_to_ui_ir` function and record
   acceptance or a typed rejection reason. A rejected lowering, command
   count mismatch, missing required image command, or a `subpixel` or
   `transform` feature tag makes that case's producer status `blocked`.
   Current integer Web layout and bounded transform approximation do not
   preserve those source semantics, even when they emit DrawIR commands.
3. Pass 500 ms to the animation case. Apply case 41's 125 px nested
   `#scroller` offset through the element-scroll API; mark it applied only if
   the resolved ID and offset match and UiIr lowering accepts every command.
   The manifest's image and SVG feature tags drive asset evidence. For cases
   29 and 30, verify the exact `checker.svg` SHA-256, bind an authored 80 × 80
   RGBA derivative through the Web image-resource API, verify its independent
   pixel digest, and require two commands bound to that exact image URI on a
   complete render. The receipt records both asset digests and the bound
   command count. Missing image commands block production;
   inline SVG decoding itself remains unverified. Case 02 stays blocked
   because its fractional dimensions and seven-degree rotation are not
   preserved. Absent pinned fonts are parity blockers where applicable.
4. Write `build/test-artifacts/simple_2d/html_css_corpus_producer.sdn`.
   Both Vulkan backend rows remain blocked until completed final-output
   captures are available from a physical Linux device. The generated receipt
   contains no screenshot golden or pixel equivalence claim.

## Scenario: preserve computed Web input

Render the pinned solid-box page at a specified animation time. Check that the
result retains the exact HTML source, reports no budget degradation, emits
more than the unconditional canvas command, and lowers to accepted `UiIr`.

## Scenario: element-scroll geometry and unsupported content

Compare the pinned case 41 and a second scroll container against unscrolled
layout. Check the requested offset, sticky top, scrollbar track and thumb,
content clipping, unchanged raw boxes, and complete UiIr lowering. A border
alone must yield no scroll range. A viewport-fixed descendant must receive
`FixedDescendantUnsupported` until fixed containing blocks are implemented.

This suite proves source execution and producer accounting only. It does not
qualify REQ-2D-006's two Vulkan outputs or NFR-2D-002.
