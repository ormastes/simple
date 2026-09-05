# Red-team audit — Modern SSpec lane modules (E1b)

Date: 2026-08-08. Target commit: `21aa9362562a13914ac40ec91be2a4876a63a71b`.
Follow-up to `modern_sspec_evidence_contract_redteam_2026-08-08.md` (core contract; four findings, fixed).

Scope: the seven lane modules landed today. **READ + PROBE only** — no source or spec was modified.
Method: probe files under `/tmp/claude-1000/-home-ormastes-dev-pub-simple/` run with
`SIMPLE_TIMEOUT_SECONDS=900 bin/simple run <probe>` (not `bin/simple test` — 800-module cap).
Every finding below quotes output that was actually executed. Items marked UNVERIFIED were reasoned
from source and not run.

Binary caveat: `bin/simple` is currently the Rust bootstrap seed (it prints the seed banner). All
observations are seed-interpreter observations; none of the defects below are engine-dependent —
each is a plain control-flow/logic fault visible in the source.

---

## F1 — BLOCKER — `manual_render.blocks_for_audience` ignores its `audience` argument

`src/lib/common/spec/evidence/manual_render.spl:188-192`

```
fn blocks_for_audience(blocks: [ManualBlock], audience: EvidenceAudience) -> [ManualBlock]:
    var out: [ManualBlock] = []
    for block in blocks:
        out.push(block)          # every block, unconditionally
    out
```

`ManualBlock` carries an `audience` field (`model.spl:429-433`) and the function's own doc comment
states "A user manual must never leak QA-only evidence (raw protocol dumps, byte tables,
troubleshooting matrices). Filtering happens here, once". No filtering happens. The parameter is
unused.

Probe `p1_manual_scene.spl` (P1a): two blocks, one `EvidenceAudience.user`, one
`EvidenceAudience.qa` titled `QA-ONLY-SECRET`, rendered with `render_blocks(blocks, user)`.

```
user render lines=8 qa_block_leaked=true
```

The QA block appears verbatim in the user manual. Every user-facing manual generated through this
renderer today leaks QA-only evidence.

Smallest fix: `if block.audience == audience or audience == EvidenceAudience.qa: out.push(block)`
(QA sees everything, user sees only `user`-tagged blocks) — one line inside the existing loop.

## F2 — BLOCKER — `scene_profile.validate_scene_assets` dangling-mesh check is `if false:`

`src/lib/common/spec/evidence/format/scene_profile.spl:177-179`

```
for obj in scene.objects:
    if false:
        findings.push("object " + obj.node_id + " references dangling mesh " + obj.mesh_id)
```

The dangling-*material* check on the next line calls `asset_exists`; the dangling-*mesh* check is
hard-disabled. The module header sells exactly this capability as its reason to exist: "a 3D scene
can pass a screenshot compare while referencing a mesh that does not exist".

Probe P1b: one object with `mesh_id: "MESH_DOES_NOT_EXIST"`, assets containing only `mat1`.

```
dangling-mesh findings=0
```

The one defect class the module was written to catch is undetectable.

Smallest fix: `if not asset_exists(scene.assets, obj.mesh_id):`.

## F3 — BLOCKER — `terminal_grid`: a region wholly outside the grid resolves "successfully" to blanks

`terminal_grid.spl:236-240` (`cell_at`) returns `terminal_cell_default()` (a space) for any
out-of-range index. `scoped_region_text_detailed` only reports `ok = false` when the region is
*absent* or has `width <= 0 || height <= 0` — never when it addresses cells the grid does not have.
The module header states the opposite rule as a load-bearing invariant: "a region that resolves to
no cells is an ERROR, not empty text, because empty text is indistinguishable from 'the region
correctly rendered nothing'".

Probe P3, on a 2x2 grid `["ab","cd"]`:

```
outside ok=true clipped=false text=<<  \n  >>     # region row=50 col=50 w=2 h=2
neg     ok=true clipped=false text=<<  \n  >>     # region row=-5 col=-5 w=2 h=2
oversize ok=true clipped=false text=<<abcd<98 spaces>\ncd...>>  # region w=100 h=100
```

A region pointing at nothing (typo'd offset, stale layout, off-by-one after a resize) yields a
blank-but-`ok` value. An oracle asserting `""` or a whitespace pattern for such a region passes
clean. The oversize case is worse: it silently *fabricates* 98 columns of content the snapshot
never had, and folds row 1's content into row 0 (`abcd` on one line) because `cell_at` indexes
`row * columns + col` with no per-row bound.

Smallest fix: give `cell_at` an out-of-range signal (return `(cell, in_bounds)`), and make
`scoped_region_text_detailed` return `ok = false` when `region.row + region.height > snapshot.rows`
or `region.col + region.width > snapshot.columns` or either origin is negative.

## F4 — MAJOR — `terminal_grid`: multi-codepoint grapheme clusters are split and silently mangled

`terminal_snapshot_from_rows` walks `while i < row_text.len()` but slices with
`row_text.slice(i, i + 1)`. `len()` counts bytes; `slice` indexes characters. For any non-ASCII
row the two disagree. Worse, a ZWJ cluster is treated as several independent graphemes, and
`display_width_of` measures only the cluster's **first** code point (`code_point_of` →
`char_code_at(0)`).

Probe P3, family emoji `U+1F468 ZWJ U+1F469 ZWJ U+1F467` in a 10-column grid:

```
family len=18 width_of_whole=2
cells=10 cols=10
proj0=<<\xf0\x9f\x91\xa8\xe2\x80\x8d\xf0\x9f\x91\xa9>> proj0.len=11
```

An 18-byte, single-column-pair cluster becomes **three separate wide cells consuming 6 columns**,
and the text projection round-trips to 11 bytes — a *different* emoji sequence (the girl is gone;
one ZWJ survived attached to a continuation cell, which the projection then drops inconsistently).
The regional-indicator flag case is the same class:

```
flag proj=<<\xf0\x9f\x87\xba\xf0\x9f\x87\xb8>>
```

`U+1F1FA U+1F1F8` is one 2-column flag glyph but is laid down as two 2-column cells (4 columns).
Any TUI evidence containing emoji, flags, or combining sequences records column positions that no
real terminal produces, and `terminal_cell_diff` will report spurious per-cell differences.

Note the combining-mark path (`:178-185`) attaches a zero-width mark to `cells[len-1]`, which for a
wide grapheme is the **continuation** cell — and continuation cells are skipped by both
`region_row_text` and `terminal_text_projection`, so the mark is dropped from evidence entirely.

Smallest fix: iterate by grapheme cluster (or at minimum by character, using a char count rather
than `len()`), treat ZWJ as *joining* the previous cluster rather than starting a new cell, and
attach combining marks to the last non-continuation cell.

## F5 — MAJOR — `binary_layout.binary_field_table` disagrees with `decode_u64` for any field wider than 8 bits

`binary_layout.spl:226-239`. The "Raw (hex)" and "Bytes" columns are both `byte_to_hex(fv & 0xFF)`
— the low byte only — and `offset_byte` is `field.lsb / 8`, the *start* byte, with no span. The
module header claims this is structurally impossible: "the same layout that drives the comparator
also drives the manual's byte/bit table — a hand-written table can silently drift from the field
set the oracle actually checks, and this makes that impossible."

Probe P4f, a 40-bit `phys_addr`-shaped field at lsb 12 holding `0xABCDEF1234`:

```
decoded wide = 737894404660
table 1 | 34 | 51:12 | wide | 34 | 737894404660
```

`Raw (hex) = 34` describes 8 of the field's 40 bits. A reviewer diffing the manual's byte table
against ground truth is reading a truncated value while the oracle checked the full one — the exact
drift the module says it prevents. (`Bytes` and `Raw (hex)` are also literally the same expression,
so one of the two columns carries no information at all.)

Smallest fix: render the full field value as hex to `ceil(width/4)` digits, and make the offset
column a byte *range* (`lsb/8 .. (lsb+width-1)/8`).

## F6 — MAJOR — `action_trace.target_resolution_is_valid` is a stub that always returns `true`

`action_trace.spl:86-90`

```
# A coordinate resolution with no recorded hit node cannot be trusted: ...
pub fn target_resolution_is_valid(target: UiTargetResolution) -> bool:
    true
```

The doc comment states the rule (`hit_node` mandatory when `resolved_by == "coordinates"`), the
helper `target_resolved_by_coordinates` exists to implement it, and `ui_action_step_is_valid` calls
the validator first — so the whole chain is wired and the leaf is empty. A coordinate-resolved click
with no hit node passes `action_trace_is_valid`. UNVERIFIED by probe (source-evident; the branch is
literally unreachable-free `true`).

Smallest fix:
`if target_resolved_by_coordinates(target): return target.hit_node != ""` then `true`.

## F7 — MAJOR — validators are decoration: no projection consults them

Probed and source-confirmed. Of the seven modules, only three gate their projection on their own
validator:

| module | validator | consulted by projection? |
|---|---|---|
| terminal_grid | `terminal_snapshot_is_valid` | yes (`terminal_snapshot_to_evidence:329`) |
| simulation_profile | `simulation_run_is_valid`, `sample_set_is_valid` | yes |
| binary_layout | `layout_errors` | yes (`decode_u64:205`) |
| scene_profile | `validate_scene_assets` | **no** |
| action_trace | `action_trace_is_valid` | **no** |
| text_protocol | (none beyond the parser) | n/a |

`scene3d_to_evidence` documents the omission as deliberate ("A scene that fails
`validate_scene_assets` still projects — the projection is a structural fact, not a pass/fail
verdict"), which is a defensible split *only if* something downstream actually calls the validator.
`action_trace_to_evidence` has no such note and no caller: probe P2 confirms a trace projects
happily, and nothing in the module or the comparator ever calls `action_trace_is_valid`. Combined
with F6 this means a timed-out settle (`settle_condition_is_valid` → false) reaches evidence
unflagged.

Smallest fix: emit the validator verdict as an evidence node (e.g. `trace.valid` / `scene.findings`)
so a closed oracle must assert on it, rather than leaving the validator as an optional side call.

## F8 — MINOR — `text_protocol` accepts an empty header key

Probe P4c, frame containing the line `: novalue`:

```
empty-key: parse_ok=true nodes=4
   response.headers. = <<novalue>>
```

The node path is `response.headers.` with a trailing dot — a selector path a spec cannot
meaningfully address, and one that would collide with any other empty-key header in the same frame.
The module rejects a header line with no colon but not a header with no name.

Smallest fix: `if key == "": return canonical_evidence_parse_error(...)` after the `to_lower(...)`.

## F9 — MINOR — `binary_layout.field_insert` silently truncates an over-wide value

Probe P4f: `field_insert(v, lsb: 1, width: 1, field_value: 3)` → the value is masked to `1`.

```
insert 3 into width-1 at lsb1: v=1 -> 3  bit2_after=0
```

Good news: it does **not** corrupt the neighbouring bit (bit 2 stays 0) — the `& mask` before the
shift contains it. The defect is that a caller writing 3 into a 1-bit field gets no signal that two
bits of intent were discarded. Same shape for `width = 0`: `extract` returns 0 and `insert` is a
no-op, both reading as clean successes (`layout_errors` does reject `width <= 0`, so this is only
reachable by calling the primitives directly, as a spec author naturally would).

`lsb 63, width 2` on `-1` returns `3` — it reads a 65th bit that does not exist. `layout_errors`
correctly rejects that field shape (`63 + 2 > 64`), so it is gated at the layout level; the
primitive itself is unguarded.

Smallest fix: these are `pub` primitives — either return `Result`, or document that callers must
pre-validate. At minimum add a `width` bounds guard (`width < 1 or width > 63` → return input).

## F10 — MINOR — `sample_percentile` clamps out-of-range `p` instead of refusing it

Probe P4g:

```
one sample:  p0=42  p50=42  p100=42
ten samples: p0=1 p50=5 p100=10 p101=10 pneg=1
```

`p = 0` → rank clamps to 1 → returns the min; `p = 101` and `p = -50` are accepted and clamped
rather than rejected. The single-sample set behaves correctly (every percentile is the sole value).
Separately, the "refused" return value is `-1`, which is a legal sample value in a signed fixed-point
metric — a caller cannot distinguish "refused" from "the p50 is -1".

Smallest fix: reject `p < 0 or p > 100`; return an `Option<i64>` (or a paired `(value, ok)`) instead
of the `-1` sentinel.

---

## What held up

These were attacked and did **not** break:

- **Empty/degenerate projections still fail closed downstream.** Probe P2: an empty `DrawScene`
  and an empty `ActionTrace` both project to `parse_ok=true, nodes=0`, but
  `compare_evidence` against an ordinary `check_exact` returns
  `FAIL / 1 check(s) failed` in both cases — the unresolved-selector rule catches it. The
  zero-positive-resolution and no-checks vacuity gates in `evidence_comparator.spl:288-340` close
  the remaining paths. Attack vector 1 is defended (F3 is the exception, and it is a *fabricated*
  value, not an empty one — which is why it gets through).
- **Zero-column terminal snapshot.** `terminal_snapshot_to_evidence` on `columns = 0` returns
  `parse_ok=false, "snapshot has no width_profile or non-positive dimensions"`. Correct.
- **text_protocol header injection via a value containing CRLF.** Probe P4a: `X-Set: a` followed by
  `X-Injected: evil` parses as two distinct header nodes with their real names — the injected line
  is visible as its own node, not folded into the first value. A colon inside a value
  (`Host: example.com:8080`) splits on the *first* colon only and preserves the value intact.
- **Body line that looks like a header.** Probe P4d: `B: 2` after the separator becomes
  `response.body.lines = <<B: 2>>`, not a header node. The separator rule holds.
- **Non-numeric status / digits in a request path.** Probe P4e and P5: `GET /404 HTTP/1.1` and
  `GET /v2/404/items HTTP/1.1` both emit **no** `status` node — the whitespace-token rule correctly
  refuses to mistake a path segment for a status.
- **Duplicate headers.** Probe P5: `Set-Cookie` twice produces two nodes at the same path, and an
  exact check against one of them fails closed on ambiguous cardinality rather than silently taking
  the last value.
- **scene_profile hit test at a rect boundary.** Probe P1c on a 10x10 rect at origin: `hit(0,0)=a`,
  `hit(9,9)=a`, `hit(10,10)=""`. Half-open interval, correct, no off-by-one.
- **Negative z.** Two overlapping hit-testable nodes at `z=-5` and `z=-10`: the `z=-5` node wins.
  The `found` flag correctly prevents the `best_z = 0` initialiser from excluding all-negative
  scenes.
- **Cyclic and missing parent chains.** Probe P1e/P1f: `draw_scene_to_evidence` projects both
  without hanging or erroring. This is correct for a flat per-node projection (it never walks the
  parent chain), but note nothing *else* validates parentage either — a cycle or a dangling
  `parent_id` is simply not a checked property anywhere in the module. UNVERIFIED whether a
  consumer walks it.
- **simulation_profile empty-timeline gates.** Probe P4h: `distribution_within` on an empty
  `SampleSet` returns `false` (refuses, does not pass vacuously), and `samples_to_evidence` returns
  `parse_ok=false`. Both correct — this was the specific attack in brief item 7 and it is defended.

---

## Verdict for the three reference examples

**Not yet safe as a set.** Per module:

- `simulation_profile` — **safe.** Every probe held; empty-set and unseeded-run paths fail closed.
  Only F10 (percentile clamping) applies, and it is minor.
- `text_protocol` — **safe with one caveat.** All four injection attacks in the brief were defended.
  Fix F8 (empty header key) before an example depends on header selector paths.
- `binary_layout` — **safe for the oracle, unsafe for the manual.** `decode_u64` is sound; do not
  ship an example whose manual shows `binary_field_table` output for a field wider than 8 bits until
  F5 lands.
- `action_trace` — **unsafe.** F6 + F7 mean an example built on it demonstrates a validation story
  that does not run.
- `scene_profile` — **unsafe.** F2 means a "dangling mesh reference" example — the module's headline
  use case — would pass while asserting nothing.
- `terminal_grid` — **unsafe.** F3 and F4 both produce *fabricated* evidence values rather than
  empty ones, which is the one shape the comparator cannot catch. A TUI example must avoid emoji
  and must keep every region strictly inside the grid until these land.
- `manual_render` — **unsafe for any user-audience example.** F1 leaks QA evidence into every user
  manual.

Recommended order: F1, F2, F3 (each is a small, local, independently landable fix), then F4/F5/F6,
then the minors.
