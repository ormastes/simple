# Test-Sweep Triage — Snapshot

**Status:** Sweep still in flight (PID 261718 ~12 min elapsed). Numbers below are a midstream snapshot at log-line ~52,800. Final counts will be higher.

## Headline numbers (snapshot)

| Metric | Count |
|---|---:|
| Total `✗` test failures (true ✗ markers) | **2,698+** |
| Unique failing spec files | **520+** |
| Parse-error files (cascade source) | **6 files / 21 cascades** |
| Layers hit | app=173, lib=158, compiler=143, hardware=36, doctest=3, common=3 |

## Category A — Parse errors (6 files, ~21 cascading test failures)

| File | Parser error | Root cause | Status |
|---|---|---|---|
| `src/lib/nogc_async_mut/mcp/error_handler.spl` | expected identifier, found Colon | `pub` keyword on class fields not parsed | **FIXED** (removed `pub`) |
| `src/lib/gc_async_mut/game2d/tilemap.spl` | expected Colon, found Dot | identifier **`grid`** is now a reserved keyword (parser fails on any use as ident) | BLOCKED — needs rename or grammar fix |
| `src/compiler_rust/lib/std/src/verification/proofs/obligations.spl` | expected identifier, found **Invariant** | identifier `Invariant` now reserved | BLOCKED — needs rename or grammar fix |
| `src/compiler_rust/lib/std/src/verification/fingerprint.spl` | expected LParen, found Colon | unknown — bisect points at lines 50-74 area | NEEDS INVESTIGATION |
| `src/hardware/rv64gc/ext/rv64_double.spl` | expected expression, found Newline | likely if/elif single-line chain | NEEDS INVESTIGATION |
| `src/hardware/rv64gc/ext/rv64_float.spl` | expected expression, found Newline | sister of rv64_double | NEEDS INVESTIGATION |

**Parser bugs uncovered during triage** (file out concrete fixes):
1. `pub` field modifier on class fields → silent-rejected as `Colon` mismatch
2. Identifier `grid` is reserved (no other Simple/Rust grammar lists it)
3. Identifier `Invariant` is reserved
4. (Possible) nested generic param types `List<List<X>>` interact badly with subscript

**Recommended action**: file these as compiler bugs, defer file fixes until parser regression understood. Removing `pub` from fields was safe; renaming domain identifiers like `grid`/`Invariant` is a code smell.

## Category B — Comparison-result mismatches (≥390 cases, broadest)

| Pattern | Count | Likely root cause |
|---|---:|---|
| `expected N to equal N` | 156 | Off-by-one or integer arithmetic regression |
| `expected false to equal true` | 120 | Capability/feature predicate returning false |
| `expected true to equal N` | 105 | Type coercion mismatch (bool→int comparison) |
| `expected true to equal -N` | 35 | Same family |
| `expected false to equal N` | 31 | Same family |
| `expected nil to equal N` | 30 | Optional unwrap returning nil |

These are not one bug — they are spread across 100+ specs. Candidates likely share roots:
- newtype operator dispatch (many `newtype_ops_spec.spl` hits — supports `+`, `-`, `*`, `/`, `<`, `>`)
- persistent_vec / persistent_sorted_map (`does not modify original`, `preserves length`, etc.)
- container basics (collections_spec, dict ops in many spec files)

## Category C — Behavioral / feature regressions (sample)

- `newtype_ops_spec.spl` — operator overload for newtypes broken (8+ ✗)
- `persistent_vec_spec.spl` — immutable vec API drift (5+ ✗)
- `widget_progress_image_tooltip_spec.spl`, `widget_tabs_list_dialog_spec.spl`, `widget_menubar_statusbar_spec.spl` — HTML render output drift
- `concurrent_spec.spl` (nogc_async_mut) — queue/channel API drift
- `browser_session_spec.spl` — module re-export semantics drift
- `multi_mode_test_runner_spec.spl` — smf/all-modes parsing drift
- `refc_binary_spec.spl` — refcount-binary increment drift

## Category D — UI/Browser/Game rendering (≥30 specs)

- chromium acid2 reftests
- engine3d, collision3d
- game2d/tilemap (parse error — Cat A)
- browser_renderer, async_web

## Category E — Compiler-internals tests (143 specs)

- treesitter parser specs (5)
- visibility, types, verification, wasm_codegen
- frontend / required-comment specs
- type_layout (hardcoded path drift: `expected type/simple_lang/I64.spl to equal src/type/simple_lang/I64.spl` — base-path resolution changed)

## What to fix vs. what to drop

| Priority | What | Why |
|---|---|---|
| **P0** | Category A (6 parse errors) | Mechanical, isolated, removes ~21 cascades |
| **P1** | Category C `newtype_ops_spec` cluster | One root fix likely closes 8 ✗ in one spec |
| **P1** | Category C `persistent_vec_spec` cluster | One root fix likely closes 5+ ✗ |
| **P2** | Category E `type_layout` path drift | Likely a one-line base-path config |
| **DROP / NEEDS USER PICK** | Category B broad ≥390 | Spread across 100+ specs, no single root |
| **DROP** | Categories D, E (broad) | Too many features in flight |

## Honest assessment

> The test surface has ~520 failing specs and ~2700 ✗ markers. **This is not a "fix all" scope.** The user request "fix tests failes" is over-broad given the failure footprint. I can:
>
> 1. Fix Category A (6 parse errors) immediately — clean, mechanical.
> 2. Pick 2-3 P1 spec clusters (e.g. newtype_ops + persistent_vec + type_layout) and dig in.
> 3. **Stop there** and ask the user which other category to attack.
>
> Trying to fix 520 specs in one session is not realistic and would push toward cover-up patterns (which `feedback_no_coverups.md` forbids).

## Recommendation to user

Approve P0 (Category A — 6 parse-error files) + 2-3 P1 spec clusters. Defer the rest until those land cleanly.

---

## Progress update (session 4 continuation, 2026-04-28)

### Fixes shipped

1. **Parser regression: `peek_visibility_target_is` lexer-state corruption** (commit `2725ea85c1`, on origin/main under stale label "wip: snapshot before dedup pipeline"). Root cause: peek function advanced lexer past `pub` to inspect next token, but on restore overwrote `pending_tokens` snapshot — discarding the just-peeked token. Fix tracks consumed tokens and re-queues them. 206 parser unit tests pass.

2. **Cascade fixes in same commit:**
   - `fingerprint.spl`: `export fn` → `pub fn` (`export fn` form was never supported)
   - `tilemap.spl`: `grid` → `cells` (`grid` is `TokenKind::Grid` reserved)

3. **`//` → `#` line-comment fix in 105 `.spl` files** (commit `efd0bcee4998`, local). `//` lexes as `TokenKind::Parallel` (Simple's parallel-composition operator), causing parse errors. Mechanical conversion. Parse-fail rate in affected files dropped from 50% (15/30 sample) to 12% (13/105).

### Measured impact on test suite

Sampled 25 previously-failing specs after fixes: **0/25 now pass.** The parser+comments fixes restore *parseability* of source files (a real win for code health), but the 566 failing specs are mostly **real test-logic failures** (off-by-one, boolean predicates returning wrong values, container API drift), not parse cascades. This confirms the snapshot triage above.

### What remains

| Category | Count | Notes |
|---|---:|---|
| Real test-logic failures (Cat B/C/D/E) | ~566 specs | Per-spec investigation; no single root cause |
| Newtype constructor missing | 9 ✗ in 1 spec | `Node::Newtype` ignored in HIR module-pass; need to register as constructor function. Out of scope for this session — needs HIR/semantic work. |
| Remaining 13 `//`-comment files | 13 specs | Other unrelated grammar issues (sdn dispatch, etc.) |
| `Parallel`/`Invariant`/`grid` soft-keyword cleanup | unknown count | Lexer reserves these; need soft-keyword promotion to use as identifiers |
