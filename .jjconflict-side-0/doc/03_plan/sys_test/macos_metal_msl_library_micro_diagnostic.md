# macOS Metal MSL Library Micro-Diagnostic Test Plan

## Scope

Exercise only the exact source-generation and Metal library-creation boundary
used by `MetalSession.init()`.

## Acceptance checks

- The emitted source hash is 64 lowercase hexadecimal characters.
- Availability, initialization, device count, device creation, and library
  creation are reported independently.
- A compiler error uses the typed C-string conversion, is single-line, and is
  bounded to 1,024 bytes.
- Created resources are destroyed.
- The checker proves compiler/provider manifest bindings, loaded-provider
  identity, wall-clock bounds, and retained-output bounds.
- No command queue, pipeline, framebuffer, CPU fallback, surface, or window is
  created.

## Execution policy

Run the source contract and helper spec first. The helper spec imports the
diagnostic module, forcing it to parse without touching Metal hardware. Run the
native micro-diagnostic only when a current trusted Metal build manifest and
its bound providers are available. Do not substitute the exhausted
full-live/window harness. The current unrun state and exact prerequisite failure
are recorded in `doc/09_report/macos_metal_msl_library_micro_diagnostic_2026-07-26.md`;
this plan is not native-execution evidence.
