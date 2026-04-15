# Cross-Module Mutable Global — Resume Doc

**Created:** 2026-04-14  
**Owner:** Agent SF (original), Agent LV (live verification update)  
**Status:** UPDATED — B1 fix verified live; partial resolution confirmed

---

## Original Problem (Agent SF)

Module-level sized arrays (e.g. the launcher's registered-apps array) do not
persist writes on baremetal Cranelift. The array is allocated at compile time
but the global pointer is not re-initialised at runtime, so writes to index
slots appear lost between module init and first use.

**Recommended fix:** B1 — auto-init via `rt_array_new` at program start,
aggregated through per-module `__module_init_*` functions.

**Owner at time of filing:** unassigned compiler agent.

---

## B1 Landing (Round 12)

B1 (`sq 2f8`) landed:  
- Sized-array globals now initialised via `rt_array_new` in a per-module
  `__module_init_*` aggregator called at program start.

---

## Live Lane Verification (Agent LV — 2026-04-14)

**Run:** `bin/simple os run --scenario=x64-desktop-test`  
**Serial evidence:**

```
[launcher] Registered: Hello World (/sys/apps/hello_world)
[launcher] Registered: File Manager (/sys/apps/file_manager)
[launcher] Registered: Terminal (/sys/apps/shell)
[launcher] Registered: Browser Demo (/sys/apps/browser_demo)
[launcher] Registered 4 default apps
...
[desktop-e2e] launcher-ready apps=4
[desktop-e2e] shortcut:ok key=meta+b app=browser_demo mode=local-fallback
```

**Conclusion:** The launcher's sized-array global IS now persisting writes
across module init. `apps=4` is reported correctly and `shortcut:ok` fires
for the Browser Demo path, confirming B1 resolved the core cross-module
mutable global initialisation bug.

---

## Status: UPDATED — CORE BUG RESOLVED

The cross-module mutable global initialisation defect described by Agent SF
is **RESOLVED** by B1.

A downstream issue remains (`hello:shortcut:fail` — Hello World launch returns
-38), but this is NOT a mutable-global initialisation failure; it is a missing
builtin-binary-registry entry for Hello World in the no-NVMe baremetal spawn
path. Tracked in `shortcut_fail_downstream_2026-04-14.md`.

**No further work required on this doc.**  
Retain for regression-lock.
