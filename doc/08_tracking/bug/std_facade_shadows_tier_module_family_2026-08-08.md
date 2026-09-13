# `src/lib/<name>.spl` facades shadow tier modules via `src/std -> lib` (family)

- **Date:** 2026-08-08
- **Status:** RESOLVED (2026-09-13) — OPEN 1 spec-locked; OPEN 2 remains, inert (theoretical, no live consumer impact) — see "Re-check 2026-09-13", 12 audited innocent
- **Area:** module resolution / stdlib surface

## Mechanism (confirmed in source and empirically)

`src/std` is a symlink to `lib`. In
`src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl`, `use std.X`
becomes `lib/X.spl` and is resolved in this order:

- step 3 — `src/lib/X.spl`  ← a top-level facade
- step 4 — tier search `src/lib/<tier>/X.spl`
  (`nogc_async_mut > nogc_async_immut > nogc_sync_immut > nogc_sync_mut > common > ...`)

**Step 3 precedes step 4**, so any `src/lib/X.spl` wins the `std.X` name outright
and hides the tier module completely.

## The discriminator (measured, not assumed)

A facade is only harmful when it has **no `export use` of the backing module**.

An explicit narrow list does **not** narrow reachability — proven on `std.io_runtime`,
whose facade lists ~50 names but where `platform_name`, `cli_arg_count`,
`is_char_device` and `cli_arg_at` (all absent from the list) still resolve and
return correct values, while a fabricated symbol returns `error[E1002]`. Once the
backing module is pulled in by any re-export, its whole surface is reachable.

So: facade with any re-export → innocent. Facade that is an independent
implementation → shadows completely.

## Audit of all 16 facades

| facade | shadows | verdict |
|---|---|---|
| `string`, `crypto`, `compute`, `hash` | — | innocent: no depth-2 tier module exists |
| `text`, `platform`, `process_monitor`, `resource_tracker`, `format_utils`, `string_core` | wildcard `export use` | innocent |
| `io_runtime`, `math_repr` | narrow-list `export use` | innocent (narrow list does not narrow — see above) |
| `math` | `common/math` | **FIXED** — `math_pow`, `math_cbrt` restored |
| `option` | `common/option` | **FIXED** — facade deleted |
| `log` | `nogc_async_mut/log` → `nogc_sync_mut/log` | **OPEN — backing module broken** |
| `pe_coff_header` | `common/pe_coff_header` | **OPEN — re-export poisons via name collision** |

## Both-directions regression evidence (`option`)

`test/01_unit/lib/common/option_spec.spl` already imports exactly the 11 shadowed
`option_*` functions, so it serves as the regression gate — no parallel spec was
authored. Run in a full worktree pinned to `origin/main`:

```
baseline (facade present):
  error: compile failed: parse: in ".../src/lib/option.spl": val binding: refutable pattern ...
  error: test-runner: no examples executed
  Results: 1 total, 0 passed, 1 failed          rc=1

after (facade deleted):
  SPEC FILE VERDICT: test/01_unit/lib/common/option_spec.spl declared>=20 executed=20 passed=20 failed=0 dropped=0
  Results: 20 total, 20 passed, 0 failed        rc=0
```

The spec could not have been passing before this change, which is corroborating
evidence that the facade was a pure regression rather than a deliberate narrowing.

## OPEN 1 — `std.log` hides 9 symbols; backing module is itself broken

`src/lib/log.spl` is a 37 KB independent implementation with no re-export. These 9
symbols exist in `src/lib/nogc_sync_mut/log.spl` and are unreachable via `std.log`:

`clear_scopes get_level get_log_level log_debug log_error log_info log_verbose set_scope_level trace`

Causal ablation on `get_level`:

```
facade present : use std.log.{get_level} -> error[E1002]: function `get_level` not found
facade ablated : same probe              -> error: semantic: method `len` not found on type `nil`
```

The ablated case is a *different* error class: the symbol resolves but the backing
module faults at run time. **Re-exporting it would poison the whole `std.log`
facade**, so this is filed rather than fixed. Fix the backing module first, then
add the re-export.

## OPEN 2 — `std.pe_coff_header` hides 30 symbols; re-export collides

`src/lib/pe_coff_header.spl` defines its own `class PeHeaderSummary` (5 fields).
`src/lib/common/pe_coff_header.spl` defines a *different* `PeHeaderSummary` and 30
public `pe_*` functions that read `.optional_header` off it.

Attempting the narrow re-export
`export use lib.common.pe_coff_header.{pe_size_of_image, pe_image_base}`:

```
before : pe_size_of_image(d) -> error[E1002]: function `pe_size_of_image` not found
after  : pe_size_of_image(d) -> error: semantic: class `PeHeaderSummary` has no field named `optional_header`
control: parse_pe_header_summary(d).ok -> GOT=false  (facade's own fn, both before and after)
```

The re-exported functions bind to the *facade's* `PeHeaderSummary`, so they fault.
Fixing requires renaming one of the two classes or merging the implementations —
out of scope for a re-export change. `src/compiler/70.backend/linker/pe_inspect.spl`
and `pe_parser.spl` are the affected consumers.

## Structural guard — considered and rejected

A `scripts/check/` guard flagging any `src/lib/*.spl` that shadows a tier module
without re-exporting its full surface would false-positive: a narrow list is
*already* sufficient (so "full surface" is the wrong test), and a wildcard
re-export can still be wrong when it collides (`pe_coff_header`). Presence of an
`export use` is not a sound proxy for correctness in either direction. Revisit only
if a third genuine instance appears.

## Method note

`unresolved use` is only a warning, so every probe **calls** the symbol and prints
the returned value, and each run is paired with a fabricated-symbol control that
must produce `error[E1002]`. Probes ran against a tree pinned to `origin/main`
containing only `src/lib` plus the `src/std -> lib` symlink, with the facade
`mv`-ed away for the ablation arm.

## Re-check 2026-09-13 (BUGFIX-10 fanout)

**OPEN 1 (`std.log`) is already FIXED in the tree** (base `f26970e9d93`):
`src/lib/log.spl:1034` now carries a narrow
`export use lib.nogc_sync_mut.log.{clear_scopes, get_level, get_log_level,
log_debug, log_error, log_info, log_verbose, set_scope_level, trace}` with a
comment explaining the circular-import and nil-guard fixes that unblocked it.
No spec previously locked this reachability path, so one was added:
`test/01_unit/lib/log_facade_scope_level_reachability_spec.spl`. TDD evidence
(bin/simple SHA `readlink -f bin/simple` -> the deployed seed hard-linked from
`/home/yoon/dev/simple/bin/simple`):

```
RED  (export-use block commented out): SPEC FILE VERDICT ... outcome=ERROR declared>=4 executed=4 passed=0 failed=4
                                        semantic: function `clear_scopes`/`set_scope_level`/`get_log_level`/`log_debug` not found
GREEN (block restored, no src change): SPEC FILE VERDICT ... outcome=OK    declared>=4 executed=4 passed=4 failed=0
```

**OPEN 2 (`std.pe_coff_header`) confirmed still open, but currently inert**:
`src/lib/pe_coff_header.spl` (32 lines, own `PeHeaderSummary` with different
fields) still shadows `src/lib/common/pe_coff_header.spl`'s 30 `pe_*`
functions with no re-export, and the class-field collision described above is
still real (`grep` confirms `class PeHeaderSummary` and `optional_header` only
in the `common/` copy). However: every current consumer of the `common/`
implementation (`src/lib/common/wine_*.spl`, the wine dynload specs) imports
it via the fully-qualified `use lib.common.pe_coff_header...` path, never
through the shadowed `std.pe_coff_header` facade path — confirmed by
`grep -rln "common.pe_coff_header"`. The only two consumers of
`std.pe_coff_header` (`src/compiler/70.backend/linker/pe_inspect.spl`,
`pe_parser.spl`) use only the facade's OWN
`PeHeaderSummary`/`parse_pe_header_summary`/`pe_rva_to_file_offset` and never
reach for the 30 `common/` functions. So the collision is real but has zero
live blast radius today; the class-merge/rename fix remains out of scope for
a bugfix-lane change (touches linker consumers) and is left OPEN, unchanged
from the original "Suggested" direction.

Status: RESOLVED for OPEN 1 (regression-locked by the new spec, commit
follows in this lane); OPEN 2 unchanged (OPEN, no live impact).
