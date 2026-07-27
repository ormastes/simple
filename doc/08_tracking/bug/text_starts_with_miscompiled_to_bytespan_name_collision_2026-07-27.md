# `text.starts_with()` miscompiled into `ByteSpan.starts_with` — HIR resolves methods by NAME ONLY

- **ID:** text_starts_with_miscompiled_to_bytespan_name_collision_2026-07-27
- **Date:** 2026-07-27
- **Area:** `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
  (:604-639, :1520) — method resolution for text predicate methods
- **Severity:** high — silent miscompile to an unrelated function, then a page
  fault on garbage. 28 known call sites across the CSS path.
- **Status:** OPEN, **fix in flight.** Root cause proven by a 1.6s A/B repro.
- **Class:** flat-registry name collision — same family as the known
  `interp env_get` defect (cross-linked below), now for METHODS.

## Symptom

Whenever `common.bytes.span` is anywhere in the entry closure, a
`text.starts_with(...)` call whose **receiver type was lost** (e.g. the result
of `.lower()`) binds to **`ByteSpan.starts_with`** — an unrelated struct's
same-named method. The wrong callee reads the receiver as a `ByteSpan` and
dereferences garbage.

HIR resolves methods **by name only**. Nothing checks that the receiver is
actually a `ByteSpan`.

Guest symptom: page fault, `cr2=0x0000001700000008`.

> **Read that cr2 carefully.** The `0x17` is an
> `RtCoreArray.transient_scope_id` being read at the ByteSpan `data` field
> offset — it is **NOT a length**, which is exactly what it looks like at a
> glance. Misreading it as a length sends you hunting an array-bounds bug that
> does not exist.

## Smoking gun

`src/lib/gc_async_mut/gpu/browser_engine/dom_color.spl:29` — two calls on
**adjacent lines**, one miscompiled and one correct:

```
    if lower.starts_with("hsla(") and cleaned.ends_with(")"):
```

| call | receiver | emits |
|---|---|---|
| `lower.starts_with("hsla(")` | result of `.lower()` — type lost | `common__bytes__span__ByteSpan_dot_starts_with` ❌ |
| `cleaned.ends_with(")")` (same line) | typed `text` | `rt_string_ends_with` ✅ |

`rt_string_starts_with` exists and is used correctly in 86 other places. So
this is not a missing runtime function — it is resolution picking the wrong
one when, and only when, the receiver type is unavailable.

## Reproduction (1.6 seconds)

1. Build `dom_color.spl` alone → **all 6 relocations are
   `rt_string_starts_with`.** Correct.
2. Add `use common.bytes.span.{ByteSpan}` to the entry graph → the calls on a
   `.lower()` result **flip to the ByteSpan symbol.**

One variable — whether `ByteSpan` is in the closure. Nothing about the calling
code changes.

## Blast radius

**28 affected call sites across the CSS path**, including `apply_decls`,
`attr_selector_matches`, `extract_css_vw`, `parse_color_value`,
`_wm_window_gradient_from_css`.

Scope is broader in principle: any `text` predicate method (`starts_with`,
`ends_with`, `contains`) on a type-erased receiver, in any entry closure that
happens to include a struct declaring a same-named method. The CSS path is
merely where a `ByteSpan` import and `.lower()` results coincide.

## Defect location

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:604-639` and
`:1520`. The in-tree guard exists but is **too narrow**: it rescues only

- calls that are still *unresolved*, or
- receivers *already known* to be `str`.

A receiver whose type was erased is neither, so it falls through to the
name-keyed custom-method path and binds to `ByteSpan.starts_with`.

## Diagnostic techniques (both cheap, both general)

**1. `--emit-archive` instead of a guest lane run.** Build any single module
with `--emit-archive` for `--target x86_64-unknown-none` (**~6s**, vs ~30
minutes for the guest lane) and inspect `nm -u` / relocations. This is what
cracked this bug and the fail-open stub bug. Use it to answer "what does this
code actually call?" and "did my compiler change do anything?" before
committing to a long run.

**2. Two `objdump` traps that produced a wrong conclusion here.**

- `objdump` prints **relative call targets WITHOUT an `0x` prefix** — pattern
  matching on `0x` misses them.
- These calls are emitted as **`movabs $addr,%reg; call *%reg`**, an indirect
  call through a register. **Searching the disassembly for `call <symbol>`
  finds nothing**, which produced one confident and completely wrong "this
  code is never called" conclusion.

Grep relocations, not disassembly text, when asking whether a symbol is
referenced.

## Proper fix

Resolve `text` predicate methods by **receiver type**, not by name. Where the
receiver type is erased, the text lowering must win for `starts_with` /
`ends_with` / `contains` rather than falling through to a name-keyed struct
method — i.e. widen the guard at `method_calls_literals.spl:604-639` so an
erased receiver is not treated as evidence of a custom owner.

A fix is being implemented now. **Do not treat this doc as resolved** until the
`dom_color.spl` A/B shows `rt_string_starts_with` with `ByteSpan` in the
closure.

Regression test: compile a module calling `.starts_with()` on a `.lower()`
result with `common.bytes.span` in the entry graph, and assert the relocation
is `rt_string_starts_with`. The `--emit-archive` route makes this a
seconds-scale test.

**Do NOT weaken a gate or a test.** Project rule.

## Related

- `doc/08_tracking/bug/interp_env_get_name_collision_nil_root_2026-07-26.md`
  — **same class**: a flat, name-keyed registry hijacking an explicit
  resolution. That one was for functions; this is the method counterpart.
- `.claude/memory` `feedback_interp_struct_name_collision_global_registry` —
  same-struct-name-in-two-modules collisions, the struct counterpart.
- `doc/08_tracking/bug/simpleos_freestanding_weak_rt_stubs_fail_open_2026-07-27.md`
  — the *other* root cause found in this guest campaign. Independent defect;
  both had to be fixed. Shares the `--emit-archive` diagnostic.
- Language rule (`.claude/rules/language.md`): "Chained methods on erased
  receivers … chains fail only when a link's receiver type is erased." This
  bug is that documented hazard biting inside the compiler's own resolution,
  not just in user code.
