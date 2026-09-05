# Tiny UI/Web/WM non-functional requirements

Status: selected by user, 2026-08-14

- NFR-001: The stripped RV32 static ELF and sum of mandatory PT_LOAD file payloads must each be at most 409,600 bytes.
- NFR-002: Any claimed dynamic profile must report and keep its cold-start mandatory module closure at most 409,600 bytes.
- NFR-003: The planned subtotal is 332 KiB with 68 KiB reserved; lane budgets cannot consume reserve without an explicit design revision.
- NFR-004: Core collections, recursion, stream stacks, DOM/CSS/layout records, damage rectangles, events, and scratch memory must have configured limits and explicit overflow results.
- NFR-005: Tiny core must not depend at compile time on optional implementation packs, host adapters, full DrawIR/WebIR, or the full compositor/web renderer.
- NFR-006: Every change reports stripped size, PT_LOAD payload, sections, top symbols, dependency closure, and per-module delta.
- NFR-007: Software rendering is the correctness oracle. Strict Vulkan claims require device execution/readback evidence and explicit failure when unavailable.
- NFR-008: Host tests precede RV32 stages; RV32 build, headless checksum, fullscreen present, physical input, module loading, and final size are distinct evidence gates.
- NFR-009: Rendering and hit testing must produce identical resolved pane geometry for the same tree and unit adapter.
- NFR-010: Parsing and command decoding must be deterministic, depth/budget bounded, overflow safe, and fuzzable.
- NFR-011: No hidden allocation is permitted after initialization in the initial no-GC profile.
- NFR-012: Every accepted capability requires executable functional evidence; placeholder or comment-only support does not count.
