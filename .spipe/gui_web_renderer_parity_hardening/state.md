# Feature: gui-web-renderer-parity-hardening

## Raw Request
$sp_dev harden and real gui lib do implement production level. No dummy or temp logic. make plan for spawn agent to do items check in pherallel. often sync gh
using simple 2d rendering with simd cpu backed.
harden with metal backed drawing and pixel color level consistency
using simple web renderer with simple 2d rendering with simd cpu backed.
harden with electron base web rendering and pixel level consistency
try from simple text to complex text and image and veriety layouts.
try css from simple to complex.
try current all html and css combinations of gui generated
each try compare to electron in pixel level. (may need to shift base and size to match)
using simple gui and electron web render

## Task Type
feature

## Refined Goal
Build production-grade renderer parity hardening for Simple GUI and Simple Web Renderer by comparing real GUI/widget and HTML/CSS render outputs from Simple 2D CPU SIMD and Metal-backed paths against an Electron/WebKit reference at pixel level across representative text, image, layout, and generated GUI HTML cases.

## Acceptance Criteria
- AC-1: Simple GUI sample rendering uses real `common.ui` widget APIs and renderer entrypoints, with no exact-sample hand-drawn button/image/text shortcuts or dummy success paths in the production render path.
- AC-2: Simple 2D CPU SIMD and Metal-backed drawing paths render the same canonical primitive/color cases within a documented pixel tolerance, with evidence artifacts proving color-level consistency.
- AC-3: Simple Web Renderer can render text, multiline text, images, buttons, nested inline/block content, and basic generated GUI widget HTML through the Simple 2D CPU SIMD backend without special-casing exact HTML strings.
- AC-4: CSS coverage includes simple-to-complex declarations for color, background, padding, margin, font size, selectors, nested selectors, and button/image widget classes, with each case producing pixel evidence.
- AC-5: A reference renderer path using Electron/WebKit/Tauri-compatible browser rendering captures the same fixture set at matching viewport dimensions.
- AC-6: A pixel comparison harness aligns viewport/base offsets when needed, computes mismatch counts/percentages and color deltas, writes machine-readable reports, and fails when mismatch exceeds documented thresholds.
- AC-7: The fixture suite covers simple text, complex text, images, buttons with icon/text, varied layouts, generated GUI HTML combinations, and at least one current realistic app/page fixture.
- AC-8: SPipe specs and generated scenario manuals document the renderer parity workflow clearly enough to run without opening source files.
- AC-9: Verification output includes commands, artifacts, and pass/fail evidence for CPU SIMD, Metal, Simple GUI, Simple Web Renderer, and reference renderer parity.
- AC-10: GitHub sync uses linear `jj git fetch` plus rebase and push, and unrelated generated/tracking files are not committed with renderer hardening changes.

## Scope Exclusions
- Full browser engine completeness beyond the documented fixture suite is out of scope for the first production hardening pass.
- Interactive browser JavaScript semantics are out of scope unless needed to render the selected static reference fixtures.
- The unrelated `doc/08_tracking/test/test_db_runs.sdn` working-copy conflict is not part of this feature.

## Phase
dev-done

## Log
- dev: Created state file with 10 acceptance criteria (type: feature).
- impl: Added first production backend-parity slice for marker-free generated GUI widget HTML.
- impl: Added live Electron generated-GUI HTML capture evidence. Current result is divergent with exact mismatch accounting, not a fake pass.
