# `use std.text.{to_int_or}` resolved cleanly for a symbol that did not exist; 31 call sites were dead on arrival

- **Filed:** 2026-08-23
- **Status:** FIXED (symbol added); the DEFECT CLASS behind it is OPEN
- **Found by:** rename/move-drift spec sweep (`app/dashboard/dashboard_serve_spec.spl`)

## The concrete defect

`to_int_or` was imported from `std.text` by **six modules** and **`std.text`
never defined it**:

| module | call sites |
|---|---|
| `src/lib/nogc_sync_mut/tmux/mod.spl` | 9 |
| `src/app/llm_dashboard/gui/tmux_panel.spl` | 11 |
| `src/app/llm_dashboard/gui/terminal_panel.spl` | 2 |
| `src/app/llm_dashboard/login_only_server.spl` | 1 |
| `src/app/web_dashboard/terminal_ws.spl` | 2 |
| `src/app/dashboard/dashboard_export_runtime.spl` | 4 (+2 in `run_serve`/`run_gui`) |

**31 call sites.** `src/lib/text.spl` is a shim (`export use lib.common.text.*`)
over `src/lib/common/text.spl`, whose export list
(`common/text.spl:61`) is `parse_i64, trim, is_empty, not_empty, contains,
escape_json, NL` — no `to_int_or`. Two *other* modules define one
(`nogc_{sync,async}_mut/database/feature_utils.spl:152`) and a third has a
private copy (`app/web_dashboard/tmux_api.spl:16`), but none of those is
`std.text`.

## Why nobody noticed — this is the part worth recording

**The bad `use` does not fail.** Measured, on the spec that exposed it:

```
outcome=ERROR declared>=6 executed=6 passed=0 failed=6
    semantic: function `to_int_or` not found
```

`executed=6`, not `executed=0`. The module imported, the spec loaded, every
example RAN, and each one died at the moment it reached a call. An import of a
non-existent symbol is silently accepted and converted into a **per-call-site
landmine**. So the six modules were not "working" — every code path that reaches
one of those 31 sites fails at runtime, and nothing at load time says so.

This is the same shape as, but distinct from, the unbacked-extern class
(`unregistered_extern_silent_nil_2026-08-01.md`): there an extern with no
runtime backing silently returns **nil**; here a `use` of a non-existent stdlib
symbol silently defers to a **call-time semantic error**. Both are absence of
link-time/import-time verification; neither is caught by any pre-push guard,
because all of them check tree structure or C syntax, never Simple symbol
resolution.

**Open follow-up (the class, not this instance):** nothing verifies that every
name in a `use ... .{a, b, c}` list is actually exported by the named module. A
ratchet in the shape of `check-unbacked-extern-ratchet.shs` would find the rest
of this population. Not attempted here — this lane was scoped to spec drift, and
a census would need its own baseline.

## Fix

Added `to_int_or` to `src/lib/text.spl`, matching the contract the 31 call sites
actually depend on rather than a plausible default. Every one of them passes a
**meaningful** default — tmux pane width `80`, height `24`, scrollback `100`,
dashboard port `3000`, HTTP `Content-Length` `0` — so a non-numeric or
overflowing field must yield **that caller's default**, never `0`, never a
crash. Implementation is fail-CLOSED via `parse_int`, which returns `nil` on
both garbage and overflow.

Note the trap avoided, documented at `feature_utils.spl:152`: an earlier body
elsewhere finished with `s.to_int() ?? default`, and that trailer *can never
fire* — the `.to_int()` intrinsic is typed `i64?` but its runtime returns a
plain `int64_t`, so overflow silently yielded `0`. `parse_int` does not have
that flaw, and the spec below pins the overflow case specifically so a future
"simplification" back to `.to_int()` turns red.

## Evidence

`test/01_unit/lib/text/to_int_or_spec.spl` (+ mirror) — 7 examples, all green.
Neuter check performed: deleting the function from `src/lib/text.spl` turns the
file `ERROR ... executed=7 passed=0 failed=7` with
``semantic: function `to_int_or` not found``, then restored. Cases pinned:
plain parse, whitespace trim, non-numeric -> default, empty -> default,
partially-numeric (`"60;rm -rf /"`) -> default **not 0**, overflow -> default
**not 0**, negative.
