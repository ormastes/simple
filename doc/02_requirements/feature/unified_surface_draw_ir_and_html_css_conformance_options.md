<!-- codex-research -->
# Feature Options — Unified Surface Draw IR and HTML/CSS Conformance

Status: Vulkan-first `DrawIrComposition -> UiIr` direction selected;
producer-model choice retained below for traceability

## Option A — Producer models to Draw IR, then packed UiIr (selected)

WebIR, GUIIR/UIIR, TUIIR, and CLIIR are architectural names for optimized
producer-owned semantic state. Each graphical producer exposes a deterministic
`*_to_draw_ir(...) -> DrawIrComposition` lowering function. Native TUI/CLI
output keeps its existing cell/text protocol and uses Draw IR only when hosted
graphically. Validated Draw IR then lowers once to a packed, backend-facing
`UiIr`; Vulkan is its first optimized executor. CUDA, HIP/ROCm, Metal, and
DirectX consume the same UiIr contract after Vulkan semantics and readback are
proven.

Pros:

- Reuses the existing canonical Draw IR schema, diff, patch, SDN, capture,
  font, and image ownership.
- Keeps compact web, widget, terminal, and CLI structures optimized separately.
- Gives Vulkan fixed-width indexed buffers without leaking Vulkan handles into
  stable UI contracts.
- Prevents CUDA/HIP, Metal, and DirectX from growing surface-specific render
  command formats.
- Smallest compatibility-preserving migration.

Cons:

- Adds one explicit Draw IR to UiIr lowering/validation step.
- Producers still have distinct semantic APIs.
- Shared semantic features require small common value types or adapters.

Effort: L/XL, about 20–40 files over staged changes.

## Option B — One shared tagged `SurfaceIr` before Draw IR (not selected)

Create one semantic union for Web, GUI, UI, TUI, and CLI, then lower it to the
existing Draw IR.

Pros:

- Uniform semantic inspection and tooling.
- Some shared style/accessibility features can be centralized.

Cons:

- Universal nodes carry fields irrelevant to most producers.
- Requires two shared IR schemas and two validation/diff stories.
- High migration and compatibility risk.

Effort: XL, about 35–70 files.

## Option C — Five public IRs implementing one lowering trait (not selected)

Create physical `WebIr`, `GuiIr`, `UiIr`, `TuiIr`, and `CliIr` types, each
implementing a shared `to_draw_ir` trait.

Pros:

- Names exactly mirror surface domains.
- Strong public type separation.

Cons:

- Duplicates command, provenance, validation, serialization, diff, and testing
  concepts.
- Largest maintenance and legacy migration burden.
- Conflicts with the existing decision that WebIR is not a second display list.

Effort: XL, about 50–100 files.

## HTML/CSS completion common to all options

After lowering parity is established:

1. Freeze versioned WHATWG/CSS/WPT manifests.
2. Replace inventory-only claims with parser, style, layout, Draw IR, and pixel
   behavior.
3. Implement by dependency order: syntax/tree construction; cascade/selectors;
   values/units; normal flow/text; positioning; flex/grid/tables; backgrounds,
   borders and generated content; transforms/compositing; animation; replaced
   elements/forms; printing and remaining modules.
4. Promote WPT-derived cases into modern SSpec system scenarios with exact
   traceability and explicit unsupported outcomes.
