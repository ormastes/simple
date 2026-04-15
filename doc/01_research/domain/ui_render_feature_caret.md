# Domain Research: Shared Render, Preview, and Config Layering

**Date:** 2026-04-03
**Scope:** external prior art for shared preview/render systems, parser/config
attachment, and layered feature deployment.

## Summary

The strongest external pattern is consistent across mature UI systems:

1. preview/render is a shared runtime capability, not a per-app flag
2. stories/previews are isolated assets with stable default fixtures
3. configuration is layered with explicit precedence
4. adapters bridge the same core render data into multiple output surfaces

## Relevant Prior Art

### 1. Storybook

Storybook treats preview as a shared component/runtime concern. Apps do not
invent their own preview protocols; they register stories against a common
rendering surface.

Useful ideas:
- shared preview engine
- stable default fixtures/stories
- documentation generated from the same preview surface

Relevance:
- `simple ui render` should use shared demo assets and common output contracts
- app-specific preview commands should delegate into the shared UI runtime

Source:
- https://storybook.js.org/docs

### 2. Jetpack Compose Preview

Compose preview treats noninteractive preview as a first-class tool surface
driven by the same UI declarations used at runtime.

Useful ideas:
- preview-specific wrappers around real UI content
- multiple preview variants from one source
- render verification without starting the full app shell

Relevance:
- shared `render` should operate on `.ui.sdn` assets and app-provided preview
  adapters without requiring full GUI startup

Source:
- https://developer.android.com/jetpack/compose/tooling/previews

### 3. SwiftUI Preview

SwiftUI preview emphasizes colocated preview declarations, but the rendering
engine remains shared and tool-owned rather than app-owned.

Useful ideas:
- preview declarations as structured metadata
- shared renderer decides where and how the preview runs

Relevance:
- the repo should separate preview intent from backend-specific launcher logic

Source:
- https://developer.apple.com/documentation/swiftui/previews-in-xcode

### 4. Tauri

Tauri uses a common desktop shell with a web-rendered frontend and explicit
adapter boundaries between shell/runtime/frontend.

Useful ideas:
- treat desktop launch as adapter selection
- avoid mixing export/preview semantics directly into desktop shell code

Relevance:
- `render` should not live inside Tauri-only flows
- desktop backends should consume render outputs from shared UI layers

Source:
- https://tauri.app

### 5. Layered configuration systems

Mature CLI/config ecosystems such as Figment, Cobra/Viper, and similar stacks
normalize precedence across:
- defaults
- config files
- environment variables
- CLI flags

Useful ideas:
- one parser surface
- one typed config object
- explicit precedence
- additive extension rather than flag duplication

Relevance:
- render config should not be split across app-local flags and env vars
- parser auto-attachment should populate one shared config object

Representative sources:
- https://docs.rs/figment
- https://cobra.dev
- https://github.com/spf13/viper

## Domain Conclusions

### Conclusion 1

`render` should be a shared runtime capability owned by `app.ui`, not a flag
added separately to each GUI-like app.

### Conclusion 2

Preview fixtures should be first-class assets. A default system verification
asset such as `examples/ui/widget_matrix.ui.sdn` follows the same role that
Storybook stories and Compose preview samples serve elsewhere.

### Conclusion 3

Configuration needs layered precedence:
1. built-in defaults
2. feature config
3. environment overrides
4. CLI overrides

### Conclusion 4

Backends should behave as adapters over a shared render core. This matches both
Tauri-style shell separation and broader preview tooling practice.

### Conclusion 5

Documentation should be generated around the shared render surface itself:
- user guide
- plan doc
- architecture doc
- test/demo assets

That keeps docs and behavior aligned.
