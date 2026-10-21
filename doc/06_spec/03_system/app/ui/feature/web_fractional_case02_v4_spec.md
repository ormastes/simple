# Web fractional case 02 DrawIR v4

Requirement trace: `REQ-2D-006`, `NFR-2D-002`. Executable scenario:
`test/03_system/app/ui/feature/web_fractional_case02_v4_spec.spl`.

The scenario feeds the pinned `02-fractional-edges.html` through
`simple_web_layout_render_html_draw_ir_fractional_result` at 640 × 480. The
strict resolver examines winning authored declarations, real node/style/layout
arrays and the complete paint inventory before returning any commands.
It rejects fractional or unresolved source geometry on the root, html, body,
or scene before trusting their integer layout boxes. A negative scenario adds
a fractional html/body offset and requires an empty composition.
Successful output must be a CPU-provenance DrawIR v4 composition with one
full-surface clipped batch and six ordered commands: canvas, html, body,
`#scene`, rotated tile, and fractional bar. Backgrounds use aliased pixel
centers; both leaves use coverage AA. The tile's affine map is built from the
winning translate and rotate tokens about its center; the bar keeps an identity
linear map with fractional translation. Commands retain source node indexes
and parent IDs. Rejection yields no batch, including when a CSS paint property
or transform function falls outside the strict grammar.
Each DOM command also retains the ordinary computed-style properties alongside
its source role and node index.

This is producer admission only. No macOS test result or physical Vulkan pixel
comparison is claimed. The current verifier has reached its three-cycle cap;
the executable scenario and native Linux backend comparison remain open.
