# Web showcase runner was internally incomplete

Status: implementation repaired; executable verification blocked.

The canonical entry imported `run_web_standards_showcase`, `showcase_resolution_dims`, and `showcase_dpi`, but `examples/06_io/ui/web_render_file_gui.spl` did not define them and referenced undefined backend/readback/font variables while rendering only 80×60 CPU SIMD.

The current repair restores those APIs, defaults to 3840×2160, routes through the production renderer, and fails closed on requested/resolved Vulkan and readback identity. Owner: web renderer/showcase lane. Unblock: run the focused spec and live showcase through an admitted deployed Stage-4 CLI, then retain the receipt.

