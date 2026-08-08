# Parser Framework Detail Design — TLDR

- Immutable contracts/model/programs: `src/lib/common/structural/parse/`
- Mutable default runtime/executors: `src/lib/nogc_async_mut/structural/parse/`
- Canonical entry: `parse_request(runtime, request) -> Result<ParseResult, ParseError>`
- One snapshot byte owner; tokens use half-open byte spans; syntax uses immutable relative-span segments and scoped references.
- One indexed `ParseActionSink`: exact count → checked scan → reserve → `emit_*_at` → validated finish.
- Scalar is the oracle; SIMD supplies only structural indexes; GPU uses total chunk transition tables and private count/scan/emit staging.
- Incremental reuse requires edit lineage plus matching region bytes, complete lexical states, grammar rule, parent fingerprint, schema, and generation.
- Semantic equality excludes backend/mode/fallback/timing telemetry and allocation IDs.
- `auto` selects an optimized mode only with matching retained parity evidence and ≥1.5× end-to-end speedup.
- Simple grammar cutover is single-source: instrument current grammar, extract it, then delete old rule bodies atomically.

```text
ParseDialect + ParseRequest -> ParseRuntime -> private executor -> indexed sink -> ParseResult
```
