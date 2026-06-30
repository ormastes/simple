# Feature: GUI Web Mobile Renderer Hardening

## Raw Request
use spipe skill, harden simple gui, web renderer with chrome, electron backe metal rendering logs. and harden ios rendering. check event handling and rendering capture and performance and animation check also. improve coverage and system tests

## Task Type
feature

## Refined Goal
Harden the Simple GUI/Web/Tauri renderer evidence pipeline so production pass claims require real Chrome/Electron/Tauri capture, Metal-backed evidence where applicable, iOS/Android mobile renderer evidence, and structured event, performance, and animation coverage.

## Acceptance Criteria
- AC-1: Production GUI/web renderer parity evidence fails closed unless the renderer matrix, layout manifest, Tauri/Chrome surface capture, backend parity, font offload, raw Metal readback, and Electron event-routing evidence are all present and passing.
- AC-2: Electron event-routing evidence proves focus, window move, maximize, title-command keyboard input, body text input, pointer down/up, and no blur/tolerance.
- AC-3: Tauri mobile renderer parity evidence requires iOS WKWebView screenshot/layout evidence with Metal markers and Android WebView screenshot/layout evidence with Vulkan/skiavk markers.
- AC-4: Tauri mobile renderer parity evidence requires explicit live mobile event, capture provenance, performance, and animation proof before the full goal is marked complete.
- AC-5: Changed evidence wrappers have executable SSpec coverage and regenerated `doc/06_spec` manuals with `0 stubs`.
- AC-6: Matching `doc/07_guide`, `.codex/skills`, and `.claude/skills` process guidance documents the current verification contract.

## Scope Exclusions
No exclusion for the full goal; this state file records focused slices as they land and does not by itself prove every GUI/Web/mobile renderer surface is complete.

## Cooperative Review
N/A for this focused slice because the change is limited to existing shell evidence wrappers, SSpec contracts, and process docs.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
- implementation: Added production GUI/web event-routing evidence to the parity wrapper and non-launching gate.
- implementation: Added Tauri mobile MDI proof validation for event routing, viewport capture, performance timer, animation frames, and CSS animation support on iOS and Android lanes.
- implementation: Added Electron production event-routing performance/animation proof to the live probe, production parity wrapper, non-launching gate, SSpec coverage, and process docs.
- implementation: Promoted Electron event-routing performance/animation rows through the aggregate GUI RenderDoc coverage audit and refreshed stale retained-performance/Metal production fixtures for the stricter gate.
