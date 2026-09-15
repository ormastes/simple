# Web-rendering perf round 11 (2026-09-13)

Continuation of rounds 5-10 (`web_perf_round{5,6,7a,7b,8,9,10}_2026-09-13.md`).
Round 10 sub-timed `cas_tail` for the first time and split it into
`tail_inline` (~247 ms net) and `tail_overflow` (~271 ms net), then tried two
designs against `tail_overflow` and measured both worse. It named what was left
to try for each. This round tried exactly those two things.

**One landed, one is an honest negative.**

- **Target B (`tail_overflow`) landed: `cas_tail` 884 ms -> 635 ms mean across
  the eight-page catalog, 4/4 A/B pairs, -28%.** The sub-timer itself reads
  **297 ms -> 126 ms** (net of the ~41 ms timer floor: **256 -> 85, -67%**), and
  `decl_tbl_hits` falls **47,182 -> 12,942**.
- **Target A (`tail_inline`) is an honest negative, measured and reverted**, and
  the reason is recorded in the source so the next round does not rebuild it.

Host: macOS (darwin 25.5.0), shared box.
Runner: `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
/Users/ormastes/simple/build/cargo-r2/release/simple run <file>`,
`SIMPLE_WEB_STYLE_COUNTERS=1 SIMPLE_WEB_PHASE_TRACE=1`
(+ `SIMPLE_WEB_TAIL_SUBTIMERS=1` for the slot 8-13 split).
Base: `origin/main` @ `c9790ff4ea4` (PR #911).

## Target B: one memoized triple per declaration block

`_normalize_final_overflow_axes` asked **twelve** questions per node — two axes
x four cascade origins through `_final_overflow_axis`, plus four
`_scrollbar_width_in_decls` — over only **four** distinct strings. Each question
paid a `decl_table_build` probe keyed on the whole multi-kilobyte merged
declaration block, an array return, and a backwards linear scan of a
several-hundred-entry table, almost always to answer "absent".

Round 10's constraint was explicit: anything that moves the TABLE across a
function boundary loses, because arrays copy on rebind in this interpreter
(that is what killed its design 1, 540 -> 868 ms). So round 11 does not move the
table. It memoizes the three ANSWERS per block:

`_overflow_triple(decls) -> [overflow-x, overflow-y, scrollbar-width]`, a
`Dict<text, [text]>` keyed on the block. The copy that crosses a boundary is
three short strings. On a hit nothing is built, probed or scanned.
`_normalize_final_overflow_axes` then does four probes and composes the same
origin precedence it always did (inline-important > important > inline-normal >
normal).

Measured over the catalog: **11,158 hits / 389 misses**.

### Equivalence spec (fixtures first, as round 9/10 established)

`test/01_unit/browser_engine/web_overflow_triple_memo_equivalence_spec.spl`
(twin at `test/unit/browser_engine/`), driving a new oracle
`simple_web_layout_debug_overflow_triple_equivalence(decls)` that runs BOTH the
memoized triple and the two scanning originals — which are kept precisely so
they can be the oracle — and compares all three answers.

31 adversarial blocks attack the memo's own assumption, that one pass over the
table can reproduce a resolver that compares each longhand's entry index against
the shorthand's: shorthand-before-longhand and longhand-before-shorthand,
duplicate shorthands and duplicate longhands (last-wins, which is why the scans
walk backwards), one-/two-/three-token shorthands, a blank shorthand value,
mixed case and padding, `overflow-anchor` and `overflow-wrap` (names that merely
CONTAIN the probed name), `scrollbar-width` first/last/duplicated, colonless
entries the table build skips, `;;;`, the empty block, and a realistic merged
block of the shape the cascade actually hands over. A second `it` replays every
block so the HIT path is exercised, not only the miss path.

**2/2 examples pass, 0 mismatches.** The spec was sabotage-checked before being
believed: swapping `parts[0]`/`parts[1]` in the shorthand split makes it FAIL
naming five blocks (`[3] MISMATCH x=auto/hidden ...`). A first sabotage attempt
(`>` -> `>=` on the index comparison) did NOT fail, correctly — distinct
property names can never share an entry index, so that edit is semantically
identical. It is recorded because "the spec passed" is only evidence when the
spec can fail on the thing being changed.

### A/B evidence

4 alternating BEFORE/AFTER pairs; both source files are swapped in place between
runs, so host-load exposure is symmetric. Controls are `sel_match` and
`sec_cascade`. Totals across the 8 pages:

| pair | side | cas_tail (ms) | sel_match | sec_cascade |
|---|---|---|---|---|
| 1 | before | 875 | 831 | 2706 |
| 1 | after | **606** | 852 | 2527 |
| 2 | before | 840 | 894 | 2780 |
| 2 | after | **615** | 973 | 2752 |
| 3 | before | 873 | 840 | 2825 |
| 3 | after | **684** | 940 | 2809 |
| 4 | before | 950 | 940 | 2946 |
| 4 | after | **634** | 907 | 2663 |

4/4 pairs improve, mean 884.5 -> 634.75 (**-28%**). The `sel_match` control
moves **against** the claim in pairs 1-3 (+2.5%, +8.8%, +12%): the after-runs
sat on a busier host and still won, so those deltas are conservative rather than
flattered. Pair 4 is the one pair whose control moves with the claim (-3.5%),
and it is also the largest delta, so it is the least attributable of the four;
the other three carry the claim on their own.

The `sec_cascade` control falls on every after-run, which is expected rather
than suspicious — `cas_tail` is a component of it, so removing work from slot 7
must show up there too. It is reported for completeness, not as an independent
control.

Per-page `cas_tail_ms`, pair 1 (overview / html / css-layout / css-paint /
forms-media / animation / evidence / tab-bar):

| page | before | after |
|---|---|---|
| overview | 5 | 3 |
| html | 119 | **65** |
| css-layout | 363 | **221** |
| css-paint | 332 | **280** |
| forms-media | 31 | 22 |
| animation | 22 | 14 |
| evidence | 1 | 0 |
| tab-bar | 2 | 1 |

Every page improves; the win is concentrated in the three heavy pages, which is
where the merged declaration blocks are large enough for the twelve lookups to
have been expensive.

Sub-timer detail, single runs with `SIMPLE_WEB_TAIL_SUBTIMERS=1` (the six extra
clock reads per node inflate slot 7 itself, so read these against the ~41 ms
floor, not against the table above):

| bucket | before | after |
|---|---|---|
| tail_overflow | 297 | **126** |
| tail_inline | 287 | 288 |
| tail_imp / tail_inlineimp / tail_display / tail_struct | 41-44 | 40-42 |
| `decl_tbl_hits` | 47,182 | 12,942 |
| `decl_tbl_misses` | 399 | 399 |

## Target A: measured, negative, reverted

Round 10 proposed extending the cascade memo over the one unmemoized
`apply_decls_without_display_on_writing_mode` call on `inline_normal`.

That was implemented, and deliberately NOT keyed on `memo_key` — that key embeds
the multi-kilobyte merged block, so keying on it would make every hit pay a
concat and a hash of that block, which is round 10's design-1 cost in a
different disguise. Instead the cascade memo's **entry index** was used: the
`st` entering the inline apply is exactly the entry the node just hit or stored,
so that index is a complete and short identity for it. `web_style_cascade_memo_store`
was made to return the index and `..._lookup` to record the index it hit.

It was then instrumented rather than assumed, and over the whole eight-page
catalog it measured:

```
inline_memo_hits=0  inline_memo_misses=51  inline_memo_skipped=0
```

The catalog carries **exactly 51 nodes with an inline `style` attribute**, every
one of them reached the memo (0 skipped), and **no two share a (cascade
identity, inline block) pair**. There is nothing for any memo to hit.
`tail_inline` read 287 ms before and 288 ms after.

So the ~247 ms is **~4.8 ms per CALL over 51 calls**, not a repeat cost: the
applier probes ~283 property names against the Style regardless of how few
declarations the inline block actually carries. Making that cheaper is an
`apply_decls` change, not a memo — and note that the presence-set optimisation
already answers absent probes in O(1), so the remaining cost is the 283 dict
probes plus the Style unpack/repack themselves.

The whole implementation is reverted; only a comment at the call site survives,
carrying the counts above.

## Gate verdicts

| gate | verdict |
|---|---|
| Draw IR sha256, 8/8 pages | byte-identical across all 8 A/B runs and every exploratory run: `5cdf8386bad82f0c 2ecbe24a29e7ef3c 76c359e483e11e84 2efd1c8c294b705e a16ea7c83d459a5a 616ad24659d7779e 4cf797f8c3a8f3a4 56097a5a1ce50dda` |
| `web_overflow_triple_memo_equivalence_spec` (new) | **2/2 pass**, 31 adversarial blocks x 2 passes (miss then hit), 0 mismatches; sabotage-checked |
| `web_template_elide_fastpath_equivalence_spec` (round 10) | 2/2 pass, unchanged |
| GPU boundary audit | `PASS — 2 frame(s) audited, host_pixel_iterations=0, readbacks_per_frame<=1, submits_per_frame<=1` |
| 53 `*selector*` / `*style*` / `*cascade*` / `*inherit*` + memo + the two equivalence specs | verdict lines **byte-identical before vs after** except the new spec itself (which cannot pass on the before side — its oracle does not exist there). 37 OK / 16 pre-existing ERROR after; 36 OK / 17 ERROR before. |

The `html` digest is `2ecbe24a29e7ef3c`, matching round 10's post-correction
sweep rather than the value recorded in its earlier table; both sides of every
pair agree, which is what the gate asserts.

## Residuals, named

- **`tail_inline` (~247 ms) is still open and is now understood**: 51 calls at
  ~4.8 ms each, dominated by the applier's ~283 property probes, not by repeats.
  A memo cannot touch it. The lead is `apply_decls` itself.
- **`_html_without_inert_template_sources` was NOT attempted this round.** A
  document that DOES contain `<template>` still pays the full per-char tag walk.
  It is deliberately deferred rather than half-done: all eight catalog pages take
  round 10's fast path, so the change has **no measurable per-page number on the
  catalog** and would need a synthetic page with an injected `<template>` to
  claim anything. It also cannot reuse round 10's oracle — that compares the
  wrapper against the walk, and rewriting the walk would put the new code on
  BOTH sides of the comparison, proving nothing. Doing it honestly means keeping
  the char-walk as a permanent reference implementation purely to be an oracle,
  which is a design cost that should be decided, not slipped in at the end of a
  round.
- **`ppc_props` (86 ms) and `ppc_rules` (85 ms)** were not attempted either.
  They are now a larger share of `pp_css` than before, since round 10 removed
  571 ms of `ppc_tmpl` from around them.
- The `group_parts` quadratic append remains measured at 0.7 ms over the whole
  catalog and remains not worth changing, per round 10.
