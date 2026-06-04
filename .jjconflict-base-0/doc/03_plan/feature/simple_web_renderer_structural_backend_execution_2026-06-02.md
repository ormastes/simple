# Plan: Structural Simple Web Renderer Backend Execution

Date: 2026-06-02
Status: planned
Owner: renderer pipeline

## Goal

Make Simple Web Renderer render from actual HTML/CSS content through a dynamic
Simple 2D backend selection path, with CPU SIMD as the reliable CPU backend and
Metal/Web/Electron/Tauri evidence used as parity references.

## Non-Goals

- No fixture hardcoding.
- No simulated button drawing that bypasses parsed HTML content.
- No tolerance/blur masking for backend parity evidence.

## Current Evidence

- Direct backend-executed reduced scene passes exact parity across
  `SoftwareBackend`, `CpuBackend`, and `MetalBackend`.
- CPU SIMD records real fill hits.
- Metal GPU frame completion and GPU-only readback are proven for clear and
  filled rectangle.
- HTML fast path still renders through a pure framebuffer path and must be
  structurally connected to backend execution.

## Work Plan

1. Fix the `Engine2D` facade mutation issue recorded in
   `doc/08_tracking/feature_request/engine2d_trait_facade_backend_execution_2026-06-02.md`.
2. Define a renderer display-list boundary for parsed HTML/CSS:
   boxes, text runs, images, form controls, clipping, backgrounds, borders.
3. Route display-list painting through `Engine2D.create_with_backend`.
4. Make backend selection dynamic-load friendly:
   software, cpu_simd, metal, web, and Tauri/simple backends resolve through one
   backend registry contract.
5. Add reference comparison fixtures:
   simple text, multiline text, image, button with image/text, CSS box model,
   and current generated GUI HTML.
6. Capture reference renderings using Electron and a browser/NodeJS path, then
   compare Simple output at fixed logical pixel dimensions.
7. Add fail-closed evidence:
   backend name, native bitmap size, scale factor, exact mismatch count,
   max channel diff, SIMD hit counters, and GPU readback status.

## Acceptance Criteria

- Simple Web Renderer output is driven by parsed HTML/CSS input.
- CPU SIMD backend renders the fixtures through `Engine2D`, not a hardcoded
  direct framebuffer shortcut.
- Electron and browser/NodeJS references are captured with explicit native
  dimensions and scale provenance.
- Tauri/simple backend comparison is documented or marked unavailable with a
  concrete reason.
- Exact parity evidence passes for reduced backend fixtures and reports honest
  mismatch counts for broader HTML/CSS fixtures until all gaps are closed.
