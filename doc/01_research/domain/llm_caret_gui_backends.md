# LLM Caret GUI Backends — Domain Research

This feature uses existing repository-owned host contracts rather than adding
another GUI toolkit. Electron is treated as a Chromium desktop host for the
same semantic HTTP application. The native lane uses retained application
state, event reduction, semantic HTML generation, Draw IR lowering, explicit
Metal backend selection, device readback, and winit presentation.

The relevant domain invariants are already captured by the repository's
accelerated shared UI architecture:

- host adapters do not own provider/application semantics;
- Web producers lower through Web layout and `DrawIrComposition`;
- Engine2D owns Metal selection, execution, and readback provenance;
- screenshots supplement input/action and post-action state evidence;
- a GPU claim requires a real backend handle and device readback, not a CPU
  mirror or fallback.

References: `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
and `doc/05_design/compiler/graphics/host_wm_shell_backends.md`.
