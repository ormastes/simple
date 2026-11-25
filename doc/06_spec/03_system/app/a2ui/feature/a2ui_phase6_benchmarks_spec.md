# System Manual: A2UI Phase 6 Streaming, Catalog Functions, Caret Interactive Store & Benchmarks

**Executable Spec:** `test/03_system/app/a2ui/feature/a2ui_phase6_benchmarks_spec.spl`  
**Native Harness:** `test/fixtures/a2ui_phase6_suite.spl` (`A2UI_VERIFY_PASS=137 FAIL=0`, `A2UI_LINT_GATE_CHECKED=18 FAIL=0`)

## Scenarios

1. **JSONL Streaming & Fail-Closed Truncation:** Feeds complete and chunked A2UI v1.0 wire envelopes through `A2uiJsonlStreamDecoder` and enforces byte, token, nesting depth, and truncation contracts.
2. **Catalog Function RPC Enforcement:** Evaluates `formatString`, `required`, and `openUrl` via `a2ui_execute_renderer_function_rpc`, preserving `functionCallId` correlation, isolated empty models when `surfaceId == ""`, `user_action` allowlists, `requiresUserActivation`, and URL safety checks.
3. **Persistent Caret Interactive Session Store:** Verifies `/a2ui`, `/a2ui draft`, `/a2ui compose`, `/a2ui hotswap`, `/a2ui select`, and `/a2ui json` persist user drafts across dynamic screen composition (`composition_revision`) and ABI-checked hot-swap generations (`code_generation`).
4. **Native Benchmark Qualification (§19.1, Stage 2 Cranelift on `release/1.0.0` `5f953c654e8`):**
   - `screen_10_us=1864`, `screen_100_us=104287`, `screen_500_us=2522505`
   - `leaf_invalidation_100_us=8`
   - `stream_30ops_whole_us=3016`, `stream_30ops_8b_chunks_us=3693` (`1.22x`)
   - `hotswap_lease_cycle_us=29`
   - `query_200rows_us=9689`
   - `journal_delta_poll_us=3`
