# Duplicate-check eager semantic native closure — 2026-07-24

Status: **OPEN (P2) — root cause now pinned to an exact line; NOT reproduced this pass**
Re-verified 2026-08-17 (wave_01 lane B) by content inspection. No native build was run
— see "Why not reproduced" below. This is explicitly NOT a reproduction claim.

## 2026-08-17 — the mechanism, at file:line

The doc previously said only "native entry-closure remains a static one-binary closure".
The precise line that decides it is now identified:

`src/compiler/80.driver/driver_source_loading.spl:444-450`

```
var lazy_import = false
if tail.starts_with("lazy "):
    lazy_import = true
    tail = tail.substring(5).trim()
val has_named_list: bool = tail.contains("{") or tail.contains("(")
if lazy_import and not has_named_list:
    continue
```

Only the **name-less** lazy forms (`use lazy M`, `use lazy M.*`, `use lazy M as a`) are
dropped from the entry closure. A **named-list** lazy import is deliberately collected
like any other import, because the names it declares must resolve statically (the
comment at `driver_source_loading.spl:466-471` states this as the intended contract, and
it was itself a fix for `unresolved name` regressions).

`src/compiler/90.tools/duplicate_check/main.spl:9-10` uses exactly the named-list form:

```
use lazy compiler.tools.duplicate_check.semantic.{run_semantic_analysis, run_semantic_analysis_local}
use lazy compiler.tools.duplicate_check.semantic_formatter.{print_semantic_text_report, print_semantic_json_report}
```

So the semantic/Ollama subgraph is pulled into the native closure **by design of the
current rule**, not by an oversight. `use lazy` on these two lines can never shrink the
native closure while that rule stands. This confirms the doc's existing "Remaining
solution" (capability-aware optional closure, or canonical runtime symbols) and rules out
the cheaper reading that the lazy marker is merely being ignored by a bug.

## Why not reproduced this pass

Reproduction needs a full standalone `native-build` with `core-c-bootstrap` through to
link. A stage-3 self-host bootstrap was running at ~98% CPU / 6.9 GB throughout this
session and is the user's stated top priority; the lane's host-etiquette rule forbids
competing native builds. No RED evidence was produced, so **no code change was made** —
per the reproduce-first contract. The failure mode is in any case a *loud* link error,
not a silently wrong result, so it is misfiled in the "silent wrong results" batch.

## Reproduction

A current-source standalone duplicate-check native build first failed while
lowering unrelated `std.nogc_async_mut.mcp.helpers_compat`. After removing the
MCP helper dependency from semantic JSON formatting, the same incremental build
reached link, proving that closure edge was removed.

The native one-binary closure still includes semantic/Ollama modules even though
their imports in `duplicate_check/main.spl` are `use lazy`. With
`core-c-bootstrap`, link then fails on hosted HTTP symbols plus existing
Dict/string runtime aliases. Logs:

- `build/mini_builds/duplicate-check-current-build.log`
- `build/mini_builds/duplicate-check-current-build-2.log`
- `build/mini_builds/duplicate-check-current-build-3.log`

## Root cause

`use lazy` defers module loading in the interpreted frontend. Native
entry-closure remains a static one-binary closure and follows referenced
semantic branches. Pure-Simple native eager loading can therefore reproduce the
same dependency expansion even when interpreted startup is fixed.

## Source repair

`semantic_formatter.spl` and `ollama_client.spl` now use the canonical
`char_from_code`/literal JSON punctuation instead of importing the full MCP
compatibility graph. Semantic imports in the CLI are lazy for interpreted
token/cosine startup. The phase-2 source contract prevents both edges returning.

## Remaining solution and evidence

Do not add a second duplicate-check implementation. The native build owner must
either support a capability-aware optional semantic closure or provide the
required canonical runtime symbols in the admitted full-CLI lane. Then build one
fresh Stage-4 CLI and run the focused phase-2 spec plus essential-tools smoke
once. The three-cycle cap for this session is exhausted; do not retry unchanged.

## Verification 2026-08-17 (w0001 compiler_spl lane)

Current source confirms the doc's "INTERPRETED SOURCE FIXED / NATIVE CLOSURE OPEN"
status. `src/compiler/90.tools/duplicate_check/main.spl:9-10`:

```
use lazy compiler.tools.duplicate_check.semantic.{run_semantic_analysis, run_semantic_analysis_local}
use lazy compiler.tools.duplicate_check.semantic_formatter.{print_semantic_text_report, print_semantic_json_report}
```

The `use lazy` markers are present, so the interpreted-frontend half is in place.
Row stays OPEN on the native side only. Not reproduced by this lane: proving the
native-closure half requires a native-build link, which needs an isolated
`CARGO_TARGET_DIR` and a live bootstrap slot; the host bootstrap had priority.
