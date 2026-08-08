# Duplicate-check eager semantic native closure — 2026-07-24

**Status:** INTERPRETED SOURCE FIXED / NATIVE CLOSURE OPEN

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
