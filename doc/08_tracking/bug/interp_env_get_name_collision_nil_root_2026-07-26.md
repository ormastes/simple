# Interpreter function registry resolves an explicit `env_get` import to a same-named function from another module

- **ID:** interp_env_get_name_collision_nil_root_2026-07-26
- **Date:** 2026-07-26
- **Area:** Rust seed interpreter — global function resolution (same defect class
  as the known struct-name collision, `feedback_interp_struct_name_collision_global_registry`)
- **Severity:** high — an explicitly imported function silently binds to a
  different definition with a different contract; any same-named stdlib pair is
  affected.
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  guarded (see below), the resolver itself is not fixed.

## What happens

`src/lib/common/encoding/font_registry.spl` imports:

```
use std.io_runtime.{env_get}
```

`std.io_runtime.env_get` is `(text) -> text` and returns `""` for an unset
variable. But at runtime inside the browser-engine module graph, the call
observably behaves as an **Option-returning** `env_get`:

| call | expected (io_runtime) | observed |
|---|---|---|
| `env_get("HOME")` (set) | `"/home/..."` | `"/home/..."` |
| `env_get("SIMPLE_ASSET_ROOT")` (unset) | `""` | **nil** |

That set-vs-unset signature matches the other stdlib definitions, e.g.
`src/lib/nogc_sync_mut/src/config.spl` `fn env_get(key: text) -> text?` (raw
`rt_env_get`, no nil→"" normalization). The stdlib has 10+ `fn env_get`
definitions across modules; which one wins appears to depend on module load
order, so the failure is graph-dependent: a minimal probe importing only
`std.io_runtime.{env_get}` gets the correct `""`, the same call inside the
browser-engine graph gets nil.

## Consequence found (now guarded)

`selected_font_asset_physical_path` passed `env_get("SIMPLE_ASSET_ROOT")` into
`_font_asset_normalized_root`, which called `root.trim()` → 
`error: semantic: method 'trim' not found on type 'nil'`. This was the entire
cause of `web_draw_ir_path_trim_on_nil_any_element_2026-07-26`: the DrawIR path
(vector_fonts=true) resolves font metrics for every `#text` node and is the only
path that reaches this lookup — the software path passes vector_fonts=false and
never gets here. `<div>x</div>` with `SIMPLE_ASSET_ROOT` unset was enough.

Guard landed in `_font_asset_normalized_root` (treat nil root as unset). The
guard is deliberately at the single chokepoint all `SIMPLE_ASSET_ROOT` reads
funnel through.

## Environment sensitivity

Any environment that exports `SIMPLE_ASSET_ROOT` (even empty) masks the crash;
any that doesn't (fresh shells, CI, the SimpleOS guest which has no environment
at all) hits it. This made the fixture suite green while every bare
`bin/simple run` repro crashed.

## Bisection trail

Receipt-probe descent, each stage confirmed by an inserted print:
`compute_styles` vector_fonts branch → `resolve_font_metrics_with_language` →
`_resolve_font_metrics_with_language_config` → `_browser_default_for_family_cached`
→ `browser_font_candidates_for_family` → `browser_bundled_font_path_for_family`
→ `selected_font_asset_physical_path` → `_font_asset_normalized_root`
(`root_nil=true`). Probed alternates ruled out: `attrs_raw` nil (all 15 HNode
fields initialized), `st.font_family` nil (printed `sans-serif`),
`families[0]` nil, arg-position `env_get` in a minimal 2-module probe.

## Reproduce

```bash
# fixed consumer (now passes):
bin/simple run probes/dg_draw_ir_min.spl              # DRAW_IR_MIN_OK
# the root defect (still open): any module graph loading both io_runtime and
# config.spl; compare env_get(unset) == nil vs == "".
```

## Proposed fix

Resolve imported names per-module (honor `use std.io_runtime.{env_get}`)
instead of through a flat global function table; or at minimum detect and
reject duplicate registrations with differing signatures at load time.

## Related

- `doc/08_tracking/bug/web_draw_ir_path_trim_on_nil_any_element_2026-07-26.md` — the consumer crash, now fixed
- `.claude/memory` `feedback_interp_struct_name_collision_global_registry` — same registry defect for structs

## STILL_PRESENT — re-verified 2026-08-17 (P2 triage, compiler lane)

`module_loader_core.spl:291-298` still registers by BARE NAME into a flat table
(`func_table_register(name, did)`); `irt_track_func_owned` exists only to stop one
module unload deleting another module entry, not to bind an import site.
`load_module_selective` (`:465-470`) likewise checks availability by bare name.
13 distinct `fn env_get` definitions still exist under `src/lib/`, so an explicit
import can still resolve to a same-named fn in another module. Shares a root
cause with `interp_class_name_collision_breaks_test_db_persistence_2026-08-10.md`
and `duplicate_type_name_collision_audit_2026-07-17.md`: flat, bare-name,
module-blind interpreter registries. NOT FIXED by this lane (P1-owned path).
