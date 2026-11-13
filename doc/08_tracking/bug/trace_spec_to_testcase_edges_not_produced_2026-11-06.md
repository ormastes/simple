# Traceability: spec->test-case trace edges are not produced

- **Filed:** 2026-11-06 (L2 tools batch; no prior record existed — this record
  created by the 2026-11-13 P3 tools lane from the batch title)
- **Status:** OPEN — blocked on the native-only extractor; no code change this
  lane
- **Area:** traceability (`src/app/traceability`, `src/lib/common/traceability`)

## Triage 2026-11-13 (P3 tools lane, work/p3-tools-20261113, base origin/release/1.0.0)

The spec→test-case edge producer exists but is **native-only by design**:
`src/app/traceability/extract/sspec_inventory.spl` declares itself "Native-only,
single-owner extraction from immutable source… destructively resets the shared
frontend arena; callers must own the native frontend exclusively for the entire
call. No thread-safe or interpreter-isolation guarantee is made." It imports the
compiler frontend (`compiler.frontend.core.parser`, lexer, AST) and therefore
cannot run under the seed interpreter or enter the lightweight checker's
closure.

The req→spec direction is already covered by `# @req` sidecar rows
(e.g. `test/01_unit/app/lsp/rename_formatting_spec.spl`), so this gap is only
the spec→test-case direction.

On this Windows lane there is no deployed self-hosted native release binary
(`bin/release/<triple>/simple` is absent; the copied `bin/simple.exe` is the
Rust seed, which refuses this closure), so the extractor cannot be executed
here and no honest edge production is possible from this host.

## Grant (host with the self-hosted native release binary deployed)

Run the traceability extraction pipeline that consumes
`src/app/traceability/extract/sspec_inventory.spl` over
`test/03_system/**/feature/*_spec.spl` and emit the spec→test-case edges into
the traceability ledger; then re-judge the must-check traceability rows. Do not
weaken the native-only contract to make it run under the interpreter — the
destructive arena reset is load-bearing.
