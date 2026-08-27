# Chromium Web Renderer Primitive Differential — Agent Tasks

Merge owner: `/root`. Final reviewer: normal/highest-capability root agent.
Shared names and SSpec helper names are frozen in the matching architecture and
test plan before implementation.

| Lane | Scope | Files | Stop condition |
|---|---|---|---|
| A: bridge package | Pinned Chromium C ABI bridge and manifest only | `tools/chromium-primitive-oracle/**` | Exports exactly v1 symbols, no direct component ABI dependency. |
| B: no-GC SFFI | Load/probe/lifetime/error conversion only | `src/lib/nogc_sync_mut/gpu/chromium_reference_oracle_sffi.spl` plus unit spec | Compiled ABI tests cover present/missing/version/repeat release. |
| C: converters | Test-only fixture, Chromium/Simple normalized projections | `test/helpers/web_chromium_reference_oracle.spl` plus integration spec | No new trace schema, WebIR, renderer, event parser, or font cache. |
| D: GPU evidence | Existing Simple DrawIR/Vulkan receipt integration only | integration/system tests and existing profile owners | Fence + device readback + no fallback, with no Chrome inference. |

Lower-model sidecars: N/A for the C ABI freeze; implementation lanes may use
Codex Luna/Claude Haiku only after the frozen names are accepted. Each agent
must report changed paths and must not touch another lane's files. No lane may
edit production web/GUI renderer logic merely to make a comparison pass.
