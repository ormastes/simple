# `wm_action_applier_spec` — 2 real product gaps, exposed once the spec stopped being dead

**Status:** OPEN — RED and left RED. The spec is correct; the product is not.
**Filed:** 2026-08-10
**Supersedes the "zero-examples" half of**
`doc/08_tracking/bug/wm_action_applier_spec_dead_on_both_legs_vulkan_order_env_get_2026-08-10.md`
(that blocker is now resolved — see
`aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md`).

## Before / after

```
before: declared>=1  executed=0  passed=0  failed=1 dropped=1 unrun=1 reason=zero-examples
after : declared>=17 executed=17 passed=15 failed=2 dropped=0
```

Identical on both executing legs:
`test/01_unit/os/compositor/wm_action_applier_spec.spl` and
`test/unit/os/compositor/wm_action_applier_spec.spl`.

The 17 `it` blocks had been dead the entire time the file claimed
`@cover src/os/compositor/wm_action_applier.spl 80%`.

## The two genuine failures

| Example | Diagnostic |
|---|---|
| `materializes shared GUI WindowManager state into SimpleOS compositor surfaces` | `semantic: class `WindowSurface` has no field named `session`` |
| `creates web windows with a Simple Web render request surface` | `semantic: function `wm_action_web_window_request` not found` |

Both are missing product surface, not spec errors:

1. `WindowSurface` needs a `session` field so shared GUI `WindowManager` state can
   be materialised into a compositor surface with its owning session attached.
2. `wm_action_web_window_request` is not defined or not exported anywhere reachable
   from the applier; the web-window creation path has no render-request surface.

## Unblock condition

Add the `session` field to `WindowSurface` and implement/export
`wm_action_web_window_request`. Then both legs go `17 total, 17 passed, 0 failed`.

## Do not

Do not delete either `it` block, and do not mark the file pending. These two
examples are the only assertions covering the session-attachment and
web-render-request paths.
