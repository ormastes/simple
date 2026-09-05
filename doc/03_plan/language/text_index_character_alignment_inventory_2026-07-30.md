# Text index alignment to CHARACTER semantics — migration inventory (Stage 0)

**Owner decision (given):** text index units align to **CHARACTER**, not
byte. This doc is the inventory and staged order. **No code changes in
this pass** — a big-bang edit across the affected population would be
unreviewable, and the population turns out to be larger and less
grep-able than assumed (below).

## READ THIS FIRST — does this invalidate the GO seed candidate?

**No, it does not invalidate it, but it does supersede part of its
evidence. Recommendation: deploy the GO candidate anyway, and do not
wait for this campaign.**

- Everything the candidate fixes is **independent of the units
  question**: optional-payload extraction, mixed-tuple element typing,
  byte-transparent slice reassembly, two-arg `index_of` existing at all,
  Result-under-interpret. Those are silent-corruption bugs live in the
  currently deployed binary today.
- What this campaign supersedes is the candidate's *evidence for the
  three text-index pinning specs*, which become historical at Stages
  2/4/5 below (`text_index_of_start`, `text_bracket_slice_byte_index`,
  and the json canary's byte counts).
- This campaign is multi-stage and each stage needs its own candidate
  regardless. Blocking deployment until it completes would leave the
  known-broken behavior deployed for the entire campaign — strictly
  worse.
- One honest consequence: `Value::StrBytes` (landed `8151c391932`) is a
  **bridge**. Under character indexing a slice can never split a
  codepoint, so the mid-codepoint fragment class is retired at the root
  by Stage 4 and the bridge becomes near-unreachable. It costs nothing
  to carry until then, and it is what makes the deployed-now candidate
  correct.

## Measured population (PROVED — scan of 33,394 `.spl` files under `src/` + `test/`)

| Pattern | Sites | Files | Migration role |
|---|---|---|---|
| `.len()` | 122,341 | 17,797 | **changes only for text receivers** |
| bracket form `[a:b]` | 12,333 | 2,783 | over-counts (see below) |
| `.substring(` | 4,695 | 891 | changes |
| `.slice(` | 4,634 | 952 | changes |
| `.index_of(` | 2,277 | 608 | changes |
| `.length()` | 2,048 | 442 | changes for text receivers |
| `.char_at(` | 1,153 | 397 | **MUST NOT CHANGE** (already chars) |
| `.bytes()` | 597 | 175 | stays bytes — the explicit escape hatch |
| `.char_code_at(` | 458 | 190 | **MUST NOT CHANGE** (already chars) |
| `.last_index_of(` | 136 | 87 | changes |

**The central finding: this migration cannot be driven by grep.** Two
reasons, both measured:

1. `.len()` has 122,341 sites, overwhelmingly on arrays/dicts/collections.
   Only the text-typed subset changes. There is no syntactic way to tell
   them apart.
2. The bracket-form count (12,333) over-counts heavily — it also matches
   dict/array/type/annotation forms. The often-quoted ~1,193 figure is
   the *text-specific* subset from an earlier targeted survey, and the
   two numbers must not be conflated.

Consequence for planning: **Stage 1 must be census tooling, not edits.**
Nobody can review or even enumerate the true call-site set without
type-directed help from the compiler.

## Implementations that must change per primitive (all lanes)

1. Rust seed interpreter — `src/compiler_rust/compiler/src/interpreter*`
   (notably `interpreter_method/string.rs`, `interpreter/expr/collections.rs`).
2. Rust seed MIR/codegen lowering — the index/slice paths in
   `mir/lower/lowering_expr_struct.rs` and the `rt_*` call selection.
3. Rust runtime — `src/compiler_rust/runtime/src/value/` string ops.
4. C runtime — `src/runtime/*.c` (`rt_slice` and friends).
5. `src/runtime/simple_core/core_string.spl` — SimpleOS / native runtime.
6. Pure-Simple stdlib text layer — `src/lib/common/string_core.spl`,
   `src/lib/common/text*`.

**Do NOT stage by lane.** Changing the interpreter alone re-creates the
byte-vs-character lane divergence that `ecc226b5136` fixed and that
`doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md`
documents — the single most expensive bug class this area has produced.
Stage by **primitive, across all six lanes in one commit per primitive.**

## Staged order (proposed)

- **Stage 0 — this doc.** Inventory, perf baselines, spec-update
  decisions. No code.
- **Stage 1 — census tooling.** A type-directed lint/diagnostic that
  reports text-typed receivers of `len`/`length`/`index_of`/
  `last_index_of`/`slice`/`substring`/bracket-slice, per file, with
  counts. This is the prerequisite that makes every later stage
  reviewable. Also fix the perf prerequisite (see the perf bug doc).
- **Stage 2 — `index_of` / `last_index_of`.** First, because their
  return value is almost always fed straight back into
  `slice`/`substring`, so a byte result plus character consumers is
  exactly the silent-corruption shape. Updates `text_index_of_start_spec`
  (see decisions).
- **Stage 3 — `substring` / `slice` methods.** Must follow Stage 2
  immediately; they are the consumers of Stage 2's output.
- **Stage 4 — bracket-slice `s[i:j]`.** The largest text subset. This is
  where the negative-step decision lands (cross-reference below) and
  where `text_bracket_slice_byte_index_spec` is replaced.
- **Stage 5 — `len()` / `length()` on text.** LAST and most dangerous:
  it is the loop bound for every scan in the codebase, so changing it
  before Stages 2-4 would break every in-flight loop mid-migration.
- **Stage 6 — cleanup.** Retire the `StrBytes` bridge if provably
  unreachable; keep `.bytes()` as the documented byte escape hatch;
  re-derive any remaining byte-count assertions.

## Cross-reference: negative-step slices (sibling lane, NOT this lane)

Owner decision: **negative STEP is not supported (Ruby model)** — it must
error and point at `.reversed()`. Negative **indices** from the end stay
legal. A sibling lane owns that error, its ADR, and error-asserting
tests; this inventory does not implement it. **Binding constraint on this
lane:** no primitive change here may make a negative step silently do
something. Any stage touching the bracket-slice path must preserve the
current behavior until that lane's error exists, then defer to it.

## Spec-update decisions (each one is a DECISION, called out, not a chore)

These specs exist precisely to catch this drift. None may be silently
rewritten.

1. `test/01_unit/bugs/text_index_of_start_spec.spl` (today 21/21 green,
   pins BYTE offsets) — **deliberate update at Stage 2.** Expectations
   recomputed for character offsets, in the same commit as the semantic
   change, with the ADR referenced in the spec header.
2. `test/01_unit/bugs/text_bracket_slice_byte_index_spec.spl` (today
   14/14, name and assertions both encode byte indexing) — **deliberate
   replacement at Stage 4**, not an edit: add
   `text_bracket_slice_char_index_spec.spl` with re-derived expectations
   and delete the byte-named file in the same commit, so the history
   shows a decision rather than a quiet drift.
3. `test/01_unit/bugs/text_negative_single_index_spec.spl` (7/7) —
   **MUST NOT CHANGE.** Negative indices stay legal. This spec is a guard
   for the whole campaign; a change here means something went wrong.
4. The json escape trio, including the canary case I added
   (`json_unicode_escape_spec.spl` and the two `js` variants) — these
   assert **byte** lengths via `.len()` (e.g. `café` is 5). At Stage 5
   those become character counts (`café` is 4). **Deliberate update at
   Stage 5**, with each changed constant re-derived from the codepoint
   sequence, not adjusted until green.
5. `test/01_unit/bugs/text_slice_substring_spec.spl` (76/76) — the
   largest byte-semantics population; expect a substantial deliberate
   update spread across Stages 3-4.

## Perf constraints

Baselines and the two measured/read findings live in
`doc/08_tracking/bug/char_code_at_quadratic_scan_and_core_string_ascii_probe_2026-07-30.md`.
Summary of the binding constraint: character indexing needs **either a
per-string byte-offset cache or an iterator-based API for hot paths**.
The lexer-perf objection to this alignment was refuted earlier, but
refuted is not free — Stage 1 must land the perf prerequisite, and every
later stage must re-measure the recorded lexer baseline.

## PROVED vs INFERRED

PROVED: the population table (single scan, counts reproducible); that
`.len()`'s 122k population is overwhelmingly non-text (inspection of the
pattern's matches); the perf numbers and method in the perf doc; that
`char_at`/`char_code_at` are already character-indexed (existing specs
plus the `core_string.spl` implementation).
INFERRED: the ~1,193 text-specific bracket-slice figure (carried from an
earlier survey, not re-derived here — Stage 1's census replaces it); the
staged order's risk ranking (reasoned from data-flow between primitives,
not measured); that Stage 4 makes `StrBytes` unreachable (follows from
character slices never splitting a codepoint, but needs the census to
confirm no byte-level producer remains).
