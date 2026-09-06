# Tiny UI/Web/WM feature requirements

Status: selected by user, 2026-08-14

- REQ-001: Provide Tiny Lib, Pane, Event, GUI, Web, Draw, software 2D, WM, and browser modules as a strict profile of existing Simple semantics.
- REQ-002: Make Tiny WM mandatory with one output, one fullscreen opaque root, bounded popups/overlays, keyboard focus, pointer focus/capture, parent-relative geometry, clipping, bounded damage, and direct presentation.
- REQ-003: Apply one relative-pane transform, clip, scroll, and inverse hit-test contract across TUI cells and GUI/Web/2D/WM pixels.
- REQ-004: Support the base components Pane, Row, Column, Stack, Text, Spacer, Divider, Border, Button, Checkbox, TextInput, List, ScrollPane, and Progress.
- REQ-005: Support the selected bounded HTML/CSS, layout, local-resource, navigation, focus, input, and scrolling profile; reject or receipt unsupported features deterministically.
- REQ-006: Use a validated compact TinyDrawStream as the mandatory execution contract. Keep full DrawIR and WebIR in optional adapters.
- REQ-007: Give every public class a stable ID, name mapping, ABI version, capabilities, factory/destructor, dependency metadata, static registration, dynamic descriptor, and full-to-tiny mapping.
- REQ-008: Deploy embedded optional functionality as feature packs rather than one library per class, while permitting per-class host isolation builds.
- REQ-009: Support linked and service Tiny WM forms behind the same `TinyWmPortV1`; use linked form for the smallest browser.
- REQ-010: Keep software 2D mandatory and make Tiny Vulkan an optional strict backend client with no silent fallback.
- REQ-011: Run a fullscreen built-in or VFS page on RV32 SimpleOS with framebuffer and input evidence staged separately from host evidence.
- REQ-012: Preserve compatible existing names through generated aliases and one authoritative component mapping manifest.
- REQ-013: Exclude desktop WM policy, JavaScript, TLS, media, advanced CSS, rich typography, unrestricted networking, and effects from the initial base closure.
- REQ-014: Produce static and dynamic registry capability parity and reject incompatible ABI/module descriptors.
- REQ-015: Expose explicit capacity, malformed-input, missing-capability, device-loss, and invalid-stream failures.
