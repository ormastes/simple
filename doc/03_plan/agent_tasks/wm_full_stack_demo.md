# WM Full-Stack Demo Agent Tasks

## Frozen Shared Interfaces

`WindowEventRecord`, `WindowStatus`, `SimpleWindow`, `SimpleGlfw`,
`WmContentKind`, `RenderSurface`, `setup_wm_full_stack_demo`,
`inject_window_event`, `check_wm_full_stack_demo_state`, and
`capture_wm_full_stack_demo_evidence`.

## Lanes

| Lane | Scope |
|---|---|
| Research sidecars | compiler, WM/rendering, sound/boards, docs, official backend semantics — merged 2026-07-29 |
| Lower-model sidecar | official domain research — merged and reviewed 2026-07-29 |
| Window/event | headless queue, GLFW adapter, capability errors |
| Content/render | content handles, GUI frame producer, nested `RenderSurface` |
| WM | routing, lifecycle, taskbar pin persistence, cleanup |
| Compiler | isolated fixtures/gates only; active compiler implementation belongs to another session |
| Evidence | executable SSpec/manual and live GLFW capture |

Merge owner and final highest-capability reviewer: Codex root agent.

Unimplemented scenario helpers must fail explicitly; silent placeholder passes
are forbidden.
