# Web Renderer Vulkan 4K Showcase Hardening — NFR Requirements

- NFR-WEB4K-001: Cold process start through first complete 3840×2160 Vulkan presentation is ≤1,000 ms on the declared admitted reference host.
- NFR-WEB4K-002: Warm redraw and tab-switch evidence publishes p50/p95; no fixed warm threshold is promoted until a real baseline exists, but regressions against the retained baseline fail.
- NFR-WEB4K-003: Every performance record binds binary/source/fixture digests, adapter/driver, viewport/scale, cache state, frame hash, timing boundaries, and max RSS.
- NFR-WEB4K-004: Missing physical Vulkan, real Chrome execution, fresh captures, or complete tab coverage is BLOCKED/FAIL, never fallback PASS.
- NFR-WEB4K-005: Startup performs no network fetch and no unbounded full-tree scan; immutable inventory/fixture data is loaded once and invalidated by digest/version.
- NFR-WEB4K-006: Focused tests cover success and failure paths; renderer/conformance regression checks execute once after convergence.

