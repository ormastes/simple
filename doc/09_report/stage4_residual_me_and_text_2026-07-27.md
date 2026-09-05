# Stage-4 residual `me` and `text` unresolved-name classes — 2026-07-27

Read-only investigation. Evidence logs (not in repo):

- `/home/ormastes/.claude/jobs/4403a7d8/tmp/stage4_repro25.log` — 1,077 errors (current, after symlink-alias fix)
- `/home/ormastes/.claude/jobs/4403a7d8/tmp/stage4_repro24.log` — 1,681 errors (before symlink-alias fix)

Error lines carry no file:line — the format is
`error: focused native-build: HIR lowering error in <module>: unresolved name: <n>`.
Source file:line below were located by grep on the sources the failing modules
resolve to. The build worktree copy of `backend_session.spl` is byte-identical to
the repo copy (`diff -q` clean), so repo line numbers are authoritative.

---

## CLASS 1 — `unresolved name: me`: **DOES NOT EXIST**. The "20 residual" is a grep artifact.

### Count

| Pattern | repro24 | repro25 |
|---|---|---|
| `grep -c "unresolved name: me"` (substring) | 20 | 20 |
| `grep -cE "unresolved name: me$"` (exact token) | **0** | **0** |

There are **zero** occurrences of `unresolved name: me` in either log. The 20
substring hits are all `unresolved name: metal_sffi_*` — the substring `me`
matching the prefix of `metal_`:

```
12  unresolved name: metal_sffi_release_uncommitted_submission
 6  unresolved name: metal_sffi_reap_submission_quarantine
 2  unresolved name: metal_sffi_quarantine_submission
```

**Conclusion:** the `me`↔`self` alias in `lower_unresolved_ident`
(`src/compiler/20.hir/hir_lowering/expressions.spl:219-231`, commit 8af2dc555960)
eliminated the class **completely**: 543 → 0, not 543 → 20. The bug doc
`doc/08_tracking/bug/stage4_me_receiver_unresolved_in_class_methods_2026-07-27.md`
can be closed as fully fixed. The alias code is confirmed present at
`src/compiler/20.hir/hir_lowering/expressions.spl:219` (`if name == "me" or name == "self":`)
and `:228-231` (`me` → `NamedVar(self_symbol, "self")`).

Recommended fix owner: **none for `me`** — closed. Re-verify with the exact-token
pattern `grep -cE "unresolved name: me$"`, never the substring form.

### The actual 20 errors: `metal_sffi_*` — SOURCE bug (facade re-export omission)

Reporting modules (repro25), 10 each:
`std.gpu.engine2d.backend_metal`, `lib.gc_async_mut.gpu.engine2d.backend_metal`
(two alias spellings of one physical module — so 10 real sites).

Import site: `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:29-30`

```
use std.gc_async_mut.io.metal_sffi.{
    ...
    metal_sffi_quarantine_submission, metal_sffi_reap_submission_quarantine,
    metal_sffi_release_uncommitted_submission
}
```

Call sites (10, matching the 20/2 tally exactly):

- `metal_sffi_reap_submission_quarantine` — `backend_metal.spl:398`, `:490`, `:563` (3 × 2 = 6)
- `metal_sffi_quarantine_submission` — `backend_metal.spl:549` (1 × 2 = 2)
- `metal_sffi_release_uncommitted_submission` — `backend_metal.spl:1231`, `:1369`, `:1468`, `:1917`, `:1981`, `:2031` (6 × 2 = 12)

Total 20. ✔

**Mechanism.** The three functions are *defined* in the no-GC **sync** tier:

- `src/lib/nogc_sync_mut/io/metal_sffi.spl:68` — `fn metal_sffi_quarantine_submission(...)`
- `src/lib/nogc_sync_mut/io/metal_sffi.spl:80` — `fn metal_sffi_release_uncommitted_submission(...)`
- `src/lib/nogc_sync_mut/io/metal_sffi.spl:91` — `fn metal_sffi_reap_submission_quarantine(...)`

They reach `gc_async_mut` through a two-hop facade chain:

1. `src/lib/gc_async_mut/io/metal_sffi.spl:3` — `export use std.nogc_async_mut.io.metal_sffi.*` (wildcard)
2. `src/lib/nogc_async_mut/io/metal_sffi.spl:9` — `export use std.nogc_sync_mut.io.metal_sffi.{ ... }` — an **explicit enumerated name list**

The middle hop's explicit list does **not** contain any of the three names
(`grep -c` over `src/lib/nogc_async_mut/io/metal_sffi.spl` = 0). The list ends at
`metal_create_swapchain` and predates the quarantine/reap additions. The
wildcard at hop 1 can only re-export what hop 2 exported, so the three names are
dropped mid-chain and `backend_metal.spl` sees them as unresolved.

**Fix owner: SOURCE.** Add the three names to the enumerated `export use` list in
`src/lib/nogc_async_mut/io/metal_sffi.spl:9`. No compiler change needed — this is
correct behaviour for an explicit re-export list.

*(Marked as inference, not proven: the compiler arguably should warn when a `use`
imports a name a facade did not re-export, rather than deferring to a
lowering-time "unresolved name". Not investigated here.)*

---

## CLASS 2 — `unresolved name: text`: **COMPILER bug — `text` missing from the primitive-cast table.**

### Count — stable across both builds

| | repro24 | repro25 |
|---|---|---|
| `unresolved name: text` (exact) | **48** | **48** |

Identical in both logs. **Independent of the import-resolution fixes** — the
total dropped 1,681 → 1,077 while this class did not move at all.

### Reporting modules (identical in both logs)

```
16  std.nogc_sync_mut.gpu.engine2d.backend_session
16  std.gpu.engine2d.backend_session
16  lib.nogc_sync_mut.gpu.engine2d.backend_session
```

Three alias spellings of **one physical file**:
`src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl` (323 lines). 16 distinct
sites × 3 module aliases = 48.

### The 16 sites — `text(x)` used as a to-text conversion call

All 16 are the call form `text(<expr>)`. (`grep -o "text(" | wc -l` = 17; one of
those is the substring inside `to_text(` at `:257`, giving exactly 16.)

- `backend_session.spl:218` — 3 sites:
  `"session id=" + text(self.id) + " kind=" + self.kind + " mode=" + self.mode + " active=" + text(self.active) + " gen=" + text(self.generation)`
- `backend_session.spl:258` — 1 site:
  `"[" + self.code + "] sid=" + text(self.session_id) + " " + self.message`
- `backend_session.spl:295` — 6 sites:
  `"frame=" + text(self.frame_id) + " session=" + text(self.session_id) + " size=" + text(self.width) + "x" + text(self.height) + " draws=" + text(self.draw_call_count) + " submitted=" + text(self.submitted)`
- `backend_session.spl:321` — 6 sites:
  `"frame=" + text(self.frame_id) + " draws=" + text(self.draw_calls) + " submit=" + text(self.submit_us) + "us present=" + text(self.present_us) + "us readback=" + text(self.readback_us) + "us total=" + text(self.total_us) + "us"`

3 + 1 + 6 + 6 = 16. ✔

### Mechanism (proven from compiler source)

This is the *same defect class* the compiler already documents and fixes for
numeric types, with `text` left out of the table.

`src/compiler/20.hir/hir_lowering/expressions.spl:285-303` — when a `Call`'s
callee is a bare `Ident` with exactly one unnamed argument, lowering consults
`primitive_cast_type_kind` and, on a hit, emits `HirExprKind.Cast` instead of a
function call:

```
val prim_kind = primitive_cast_type_kind(callee_ident_t)
if prim_kind.?:
    ...
    return HirExpr(kind: HirExprKind.Cast(...), ...)
```

`src/compiler/20.hir/hir_lowering/expressions.spl:60-79` — the table covers
**only** fixed-width numerics; there is no `text`/`str` arm:

```
case "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "f32" | "f64"
case _: nil
```

Its own docstring states the exact failure mode being hit here: *"These names are
not in the value symbol table, so lowering them as ordinary callees yields
`HirExprKind.Error`."*

`text` is also absent from the name-dispatched builtin list
`is_interp_builtin_fn` (`expressions.spl:51-58`), which carries `to_string`,
`str`, and `int` but **not** `text`. And there is no free function `fn text(...)`
anywhere in `src/` (`grep -rn "^fn text(\|^export fn text("` → 0 hits).

So `text(x)` in call position: not a cast (not in the table), not a builtin (not
in the list), not a user symbol (no definition) → falls through to
`lower_unresolved_ident` → `unresolved name: text`.

Note the asymmetry that makes this a compiler bug rather than a source bug:
`text` **is** accepted as a type name at
`src/compiler/20.hir/hir_lowering/types.spl:463`
(`case "text" | "str" | "String": HirTypeKind.Str`). The type checker knows
`text`; the cast table does not.

### Latent blast radius

10 other files use the same `text(<expr>)` form and will hit this the moment
they are lowered (refined scan `grep -rnE '(^|[^a-zA-Z0-9_.])text\([^:)]' src/lib`):

`src/lib/nogc_sync_mut/game2d/render/draw_batcher.spl` (3),
`src/lib/nogc_sync_mut/game2d/render/texture_atlas.spl` (2),
`src/lib/nogc_sync_mut/game2d/render/canvas.spl` (1),
`src/lib/nogc_sync_mut/play/locator.spl` (1),
`src/lib/nogc_async_mut/play/locator.spl` (1),
`src/lib/gc_async_mut/play/locator.spl` (1),
`src/lib/gc_async_mut/gpu/browser_engine/dom.spl` (1),
`src/lib/gc_async_mut/gpu/browser_engine/script/canvas_api.spl` (1),
`src/lib/common/ui/builder.spl` (1),
`src/lib/common/render_scene/scene.spl` (1).

### Fix owner: **COMPILER**

Add a `text`/`str` arm to the conversion path. Because `text(x)` is a *stringify*,
not a bit-level numeric cast, the correct landing spot is likely a separate arm
that lowers to the to-text runtime call rather than reusing
`primitive_cast_type_kind` (whose contract in its docstring is "pure numeric
casts"). Either:

1. extend `primitive_cast_type_kind` at `expressions.spl:60` with
   `case "text" | "str": HirTypeKind.Str` and confirm `HirExprKind.Cast` to `Str`
   lowers to a stringify in MIR (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2875`
   already references this comment and is the place to check); **or**
2. add `text` to `is_interp_builtin_fn` (`expressions.spl:51`) alongside the
   existing `to_string`/`str` and route it to the same builtin tag.

Option 2 is the smaller change and matches the existing `str` precedent.
Deciding between them requires reading the MIR side — not done here (read-only,
no builds).

A source-side workaround (`.to_text()` instead of `text(...)`, already used at
`backend_session.spl:257`) exists but should not be the fix: `text` is a
first-class type name the type checker already accepts, so rejecting it in call
position is a compiler inconsistency, and the same idiom is spread across 11
files.

---

## Summary table

| Class | repro24 | repro25 | Stable? | Modules | Owner |
|---|---|---|---|---|---|
| `me` (exact) | 0 | 0 | — (never existed) | none | closed |
| `metal_sffi_*` (the real 20) | 20 | 20 | yes | `backend_metal` | **source** — facade list |
| `text` | 48 | 48 | **yes** | `backend_session` | **compiler** — cast/builtin table |
| total errors | 1,681 | 1,077 | — | — | — |

Both classes are fully independent of the import-resolution/symlink-alias fixes
that moved the total from 1,681 to 1,077.
