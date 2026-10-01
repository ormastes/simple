# Web renderer cold-pipeline perf, round 3 — macOS, 2026-09-13

Interpreter `/Users/ormastes/simple/build/cargo-r2/release/simple`,
`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0`,
`SIMPLE_WEB_STYLE_COUNTERS=1`, viewport 900x760, one render per page, all eight
`examples/06_io/ui/web_catalog/*.html` in ONE process.

Instrument: `build/perfbench/pipeline_bench.spl` (+ `run.sh`, `specs.sh`) —
uncommitted lane tools, `build/` is gitignored. Same oracle as round 2: per-page
`sha256` (first 16 hex) of the complete `draw_ir_to_sdn(composition)` text.

**Honest caveat, stronger than round 2's.** Wall-clock on this host varied ~2x
between runs of identical or near-identical trees (`css-paint` measured 28.7 s,
13.6 s and 25.7 s). The per-page `pipeline_ms` column is therefore informational
only. Every claim below rests on counter buckets measured **within one run**,
where host load is common to all buckets.

## Target 1 — `Style.inherited_digest()`: measured, and the round-2 hypothesis is disproven

Round 2 flagged this ~70-part concatenated string (built per node,
`..._style.spl:518`) as an unattributed cost sitting outside every `sec_*`
bucket. It is now attributed: a ninth counter bucket, `sec_digest_ms`, wraps the
digest call and the interning block that consumes it
(`..._core.spl:3419`, `_wsc_add_section(8, ...)`).

| page | `sec_digest_ms` | pipeline share |
|---|---|---|
| overview | 6 | 0.5% |
| html | 111 | 1.3% |
| css-layout | 207 | 1.2% |
| css-paint | 177 | 1.3% |
| forms-media | 26 | 1.1% |
| animation | 20 | 0.9% |
| evidence | 1 | 0.3% |
| tab-bar | 2 | 0.4% |
| **total** | **550** | **~1.2%** |

The consumer is `style_inherit_index` / `style_inherit_ids`: the digest is
interned to an integer, so only equality matters. The obvious cheaper key — an
`inherited_equals(parent)` field-compare fast path reusing the parent's id when
nothing inherited changed — was implemented and measured: `sec_digest_ms` moved
550 -> 545 across the eight pages, i.e. nothing, and per-page it moved in both
directions. The likely reason is that under this language's copy-on-bind `class`
semantics, `st.inherited_equals(styles[nd.parent])` copies the 176-field parent
`Style` into the parameter, so a full Style copy is paid to avoid a 70-part
string. **The fast path was reverted and is not in this change**; 75 lines of
field list mirrored from `inherited_digest()` is a real maintenance hazard to
carry for a no-op. What ships is the timer, so the next round starts from a
number instead of a hypothesis.

## Target 2 — `sec_inherit_ms`: the 176-argument constructor, memoized

`renderer_default_style()` (`..._style.spl`) is a 176-argument `Style`
constructor literal containing ~90 string literals. It was evaluated once per
element inside the `sec_inherit` block (`..._core.spl:2939`). It is now built
once per process into a module-level `Style?` memo and copied on every read
(`_renderer_default_style_build()` holds the literal).

Safety rests on a measured language fact, not an assumption: a 10-line probe on
this exact binary confirmed `class` values copy on bind — module-var read,
array-element read, and a `me` method mutating the copy all leave the original
untouched. The only reference-shaped field, `resolved_font_advances`, is never
mutated in place anywhere in the tree (every writer assigns a whole new array),
so the shallow copy cannot alias. Empirically: all eight pages render in ONE
process with `inherit_from` mutating `st` on every node — if `st` aliased the
memo, pages 2-8 would diverge. They do not (8/8 digests identical).

**Evidence (temporary sub-buckets inside `sec_inherit`, removed before landing;
both columns are the SAME bucket, so host load cancels):**

| page | `tmp_default_ms` before | after | delta |
|---|---|---|---|
| html | 120 | 33 | -73% |
| css-layout | 228 | 32 | -86% |
| css-paint | 185 | 41 | -78% |
| forms-media | 29 | 8 | -72% |
| animation | 26 | 5 | -81% |
| **8-page total** | **~597** | **~147** | **-75%** |

## What round 3 found for round 4 (measured, not fixed)

The same temporary sub-buckets attribute `sec_inherit` itself. On `html`
(`sec_inherit_ms=1243`): `presentational_attr_decls` + `apply_decls` **553 ms
(45%)**, `tag_defaults` **243 ms (20%)**, `inherit_from` 93 ms (7%),
`renderer_default_style` 33 ms (3%), remainder ~25% unattributed — which
includes `val parent_style = styles[nd.parent]`, another full 176-field Style
copy per node. `css-paint` is the same shape (`tmp_pres` 872 of 1744).
**`presentational_attr_decls`/`apply_decls` is round 4's target**, and the
per-node whole-Style copies are the structural item behind it.

## Gates

- Draw IR digests: **8 of 8 byte-identical** before vs after
  (`5cdf8386bad82f0c`, `85a685ca46fc3527`, `76c359e483e11e84`,
  `d9a0d2a7e71a2960`, `a16ea7c83d459a5a`, `616ad24659d7779e`,
  `4cf797f8c3a8f3a4`, `56097a5a1ce50dda`).
- Neighbouring specs (`*style*` / `*cascade*` / `*inherit*` under
  `browser_engine`, `rendering`, `render_opt` — 19 specs): exit code and
  timing-stripped output digest **identical on both sides**, run on this tree and
  then on `origin/main`'s copies of the three files. Three are RED on both sides
  and were already RED at `origin/main`
  (`be_dom_event_path_and_style_serialize_spec`, `style_animation_spec`,
  `simple_web_css_cascade_spec`) — pre-existing, untouched by this change.
- `SIMPLE_BIN=<interpreter> sh scripts/check/check-web-vulkan-gpu-boundary-audit.shs`:
  see the PR body for the verdict of the run made against this tree.
