# Text-index alignment — addendum: scanner taxonomy, Workstream A demotion, sentinel facts

Companion to `text_index_alignment_rescope_2026-07-30.md`. Reads-only
findings. **Everything unresolved is marked unresolved** — this doc
deliberately does not fill in the four scanner bodies nobody has read.

## Workstream A (delete the private re-implementations) is DEMOTED

Re-scoped from "do this first" to **post-alignment cleanup**, for two
fully independent reasons. Either alone justifies the demotion.

**Reason 1 — it is not deduplication; it is rerouting.**
`src/lib/common/string_core.spl`'s `str_index_of` is a one-line wrapper:

```
fn str_index_of(s: text, sub: text) -> i64:
    rt_string_find(s, sub)
```

`rt_string_find` is backed by the byte-parallel SSE2 path in
`runtime_simd_search.c` (SSE2 `_mm_cmpeq_epi8` over 16 bytes/iteration,
returning `result - haystack`). So substituting the private scanners
does not merge duplicate code — it **moves those call sites onto a
different implementation**. Worse, it is actively counterproductive for
the two unit-agnostic scanners (`_sdn_index_of`, `_css_index_of`): they
are built on `len`/`substring`/`slice` and therefore migrate *for free*
when those primitives align, whereas `rt_string_find` is the one
implementation that cannot follow character alignment without a
boundary conversion. Deleting them would remove them from the free
migration and bind them to the hardest case.

General form worth carrying: **deleting a reimplementation in favour of
"the shared one" is only deduplication if both compute the same thing
the same way — read what the wrapper wraps.**

**Reason 2 — confirmed divergent edge behaviour (empty needle).**
Nominated in advance as the likeliest way a mechanical deletion goes
wrong, then checked:

| Implementation | empty needle returns |
|---|---|
| `rt_string_find` | **0** |
| `_css_index_of` | **`start`** |

A mechanical substitution would have silently changed empty-needle
results at every `_css_index_of` call site. Lesson recorded: check the
edge you nominate as most dangerous *before* substituting, not after.

## Scanner shape taxonomy — 3 confirmed shapes, 4 UNREAD

Bodies actually read (4 of ~8):

**Shape 1 — primitive-looping (unit-agnostic by construction).**
Indexes in the same unit it returns, so it inherits whatever the
primitives mean and migrates automatically *provided `len` +
`substring` + `slice` move together*.
- `src/lib/common/sdn/parser.spl` `_sdn_index_of` — `while i < s.len()`,
  `s.substring(i, i + 1) == ch`, returns `i`.
- `src/app/ui_edit/main.spl` `_css_index_of` — `haystack.len()`,
  `haystack.slice(i, i + nlen) == needle`, returns `i`. (Empty-needle
  edge diverges from the stdlib primitive — see above.)

**Shape 2 — length-and-split-derived.** Computes a *length*, not an
index, and composes it back into an offset.
- `src/compiler/90.tools/sffi_gen/intern_codegen.spl` `index_of` —
  `s.contains(needle)` guard, then `s.split(needle)`, returns
  `parts[0].len()`.
- same file, `index_of_from` — takes `start`, does `s[start:]` (a
  **bracket slice**), delegates to `index_of`, returns `start + idx`.

**Shape 3 — thin wrapper over a runtime symbol.**
- `src/lib/common/string_core.spl` `str_index_of` → `rt_string_find`
  (the SIMD byte path).

**UNREAD and therefore UNCLASSIFIED (4)** — do not assume a shape:
- `src/app/cli/query_ast_query.spl` `_index_of_from`
- `src/app/cli/query_sem_query.spl` `_index_of_from`
- `src/app/dashboard/dashboard_collectors.spl` `index_of_from`
- `src/compiler/80.driver/driver_source_loading.spl` `_driver_text_index_of`

**Why they must be read, not inferred:** of the four bodies read so far,
**two did not match the shape inferred from their signatures** — a 50%
miss rate. All of these take `text` and return `i64`; that tells you
nothing about whether the body indexes, splits, or delegates.

## `rt_string_find` sentinel facts (PROVED)

- **Not-found returns `-1`, as a raw `i64` — never nil.**
  (`compiler_rust/runtime/src/value/collections.rs:2732`, several
  `return -1` paths.)
- **Empty needle returns `0`.**

Consequence — **`index_of(..) ?? -1` would be doubly wrong**: redundant,
because the primitive already returns `-1`; *and* corrupting, because
`??` on a raw `i64` treats the value **3** as nil, so a genuine match at
index 3 would be reported as not-found. A redundant guard that
introduces the exact failure it appears to prevent.

**Clean negative (recorded so nobody re-hunts it): zero occurrences of
`index_of(...) ??` anywhere under `src/`** (specs excluded). The hazard
is real and the `??`-on-raw-i64 pattern exists elsewhere in the repo,
but no `index_of` call site pairs with it today. Nothing to fix.

## Named hazard instance: `index_of_from`

`intern_codegen.spl`'s `index_of_from(s, needle, start)` is the concrete
instance of the **offset-parameter unit drift** hazard: it accepts
`start` in one unit and returns `start + idx` in the same unit, composed
across a bracket slice and a `len`-derived offset. Migrate the parameter
and the return value in the same commit or it drifts silently — and the
drift only shows up with a **non-zero `start` on multi-byte input**,
which is precisely the two-argument path that only began existing at
`38cb691ad082`.

## Open items (all unresolved)

1. The four unread scanner bodies above.
2. `len`/`length` definition census — the real critical path for sizing;
   the "80% of migration-relevant call sites" figure comes from the
   quarantined biased census and must be re-derived.
3. Census re-run accounting for the `compilability.rs` gate (Stage 4's
   bracket population cannot be quoted until then).
4. The SIMD boundary-conversion strategy (convert once per call, not per
   comparison) is recommended but **unmeasured**.
