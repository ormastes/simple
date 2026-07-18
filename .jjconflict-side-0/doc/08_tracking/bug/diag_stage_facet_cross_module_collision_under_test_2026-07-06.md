# std.diag dbg_stage() aborts under `bin/simple test` when co-compiled with the browser_engine/host_compositor module graph

**Date:** 2026-07-06
**Severity:** medium — blocks writing `bin/simple test` specs that prove
real `dbg_stage()` emission for task #15 remainder item 3 ([browser] stage
logs); does not affect `bin/simple run` or production behavior.
**Status:** OPEN — repro isolated, root cause not fixed (out of bounds for
task #15 remainder: fix belongs in the compiler's cross-module symbol
resolution, not in src/app/ui.browser/** or host_compositor).

## Symptom

Any spec file that combines:
1. `use std.spec.*` (the wildcard every `*_spec.spl` file uses for
   `describe`/`it`/`expect`)
2. an import that pulls in the browser_engine/`os.compositor.host_compositor_entry`
   module graph (directly, or transitively via `app.ui.browser.app`'s own
   `use os.compositor.host_compositor_entry.{...}`)
3. `std.diag.dbg_force_facet(...)` forcing any facet on
4. a real `std.diag.dbg_stage(...)` call while that facet is on

aborts the whole `it` block with:

```
semantic: type mismatch: comparing string with integer
```

This reproduces under `bin/simple test <spec>` regardless of how many names
are explicitly imported from `std.diag` (a full explicit import list —
matching `test/01_unit/lib/nogc_sync_mut/diag_spec.spl`'s working set —
does NOT avoid it once the host_compositor/browser_engine graph is also
present). It does **not** reproduce under
`SIMPLE_EXECUTION_MODE=interpret bin/simple run <script>.spl` with the
identical imports and logic — confirmed via direct A/B repro (same file
content, `run` succeeds, `test` aborts).

## Minimal repro

```
use std.spec.*
use os.compositor.host_compositor_entry.{HostBackendKind}
use std.diag.{dbg_stage, dbg_force_facet, dbg_diag_reset, dbg_stage_history}

describe "repro":
    it "aborts":
        dbg_diag_reset()
        dbg_force_facet("stage")
        dbg_stage("probe", "hello")
        expect(dbg_stage_history().len()).to_be_greater_than(0)
```
Run via `SIMPLE_EXECUTION_MODE=interpret bin/simple test <this file>` →
aborts with the error above. Dropping either the `os.compositor.host_compositor_entry`
import or the `std.spec.*` wildcard (replacing it with the concrete
`describe`/`it`/`expect` imports it re-exports) makes it pass — confirmed
by isolating each ingredient independently during this investigation.

## Why it matters

Same bug class already ledgered under
`doc/08_tracking/bug/interp_cross_module_struct_field_collision_2026-07-04.md`
and the `_clamp_byte`/`_hex_pair`/`_read_u32_le`
`compiler_cross_module_private_symbol_collision` warnings printed at the
top of every `bin/simple test` run in this repo: when many modules
co-compile into one test unit, some private/public top-level symbol
(function or enum) collides across modules and the wrong co-compiled
definition is dispatched. Here the collision lands inside `dbg_stage()`'s
own body (a ~15-line function with no string/int comparisons in its
source), so the miscompiled callee is almost certainly something `dbg_stage`
calls transitively (`_emit` → `lib.log.log_dispatch_text` /
`subsys_from_scope`) picking up an unrelated same-named helper from the huge
browser_engine graph.

A related, separately-confirmed instance in the same graph: `enum
Capability` is defined 4x across `src/lib/common/ui/capability.spl` and
`src/lib/nogc_sync_mut/{security/enforcement,fs_driver,storage}/capability.spl`;
calling `BrowserApp.run_once()` (which renders a real frame) aborts with
`semantic: unknown variant or method 'Mouse' on enum Capability` under both
`run` and `test`. Also witnessed in the same investigation (test-mode
only): `enum LayoutKind` is defined 2x
(`src/lib/common/ui/widget_kind.spl` vs
`src/compiler/30.types/_TypeLayout/layout_core.spl`), surfacing as
`semantic: unknown variant or method 'Vbox' on enum LayoutKind`.

## Workaround used (task #15 remainder item 3)

`test/01_unit/app/ui/browser_shared_wm_and_stage_log_spec.spl` proves the
default-off contract (facet off → zero dbg_stage_history entries, which
does not touch the crashing path) and documents — with a manual
`bin/simple run` verification recorded in its header comment — that the
four `[browser]` stages (`parse_start`/`parse_done`/`backend_create_start`/
`backend_create_done`) fire correctly with the facet forced on. It does not
include a `bin/simple test`-executable assertion for the facet-forced-on
case, since that combination cannot currently pass.

## Next step

Find where `dbg_stage`'s transitive callees (most likely `lib.log`'s
`log_dispatch_text`/`subsys_from_scope`, or a shared string-processing
helper) resolve unqualified/private symbol names when co-compiled with the
browser_engine graph, and make resolution key off of the declared
module+type rather than name (same architectural fix needed for the
`Capability`/`LayoutKind` enum collisions and the already-ledgered `Style`
vs `CellStyle` struct collision). This is compiler/interpreter work, not
`src/app/ui.browser/**`.
