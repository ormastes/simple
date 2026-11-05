# Block error span source metadata loss

Status: OPEN; draft source qualification.

Latest release_phase3 707e6ca3d already repairs the original b2 runtime-type-array annotation, imports and span length. Its error_at/error_span still overwrite payload_span.file with empty text. Preserve the original file and use tuple fields without changing offset policy.

Exact root-owned actual source and real native fixture compiled against recovered bootstrap seed445c: archive34974B, strict matched-runtime executable25131760B. Execution exited0 with exact stdout `block error span native PASS`, empty stderr, eight assertion groups covering nonzero offsets, file, length, range and empty spans. This is focused bootstrap evidence only; Rust seed was not used for production tests.

Persisted SSpec UNEXECUTED. Full self-hosted compiler/lib/MCP/LSP checks and smoke UNEXECUTED; no overall STATUS: PASS or release admission. Reversed/out-of-range policy unchanged. Original source b2 immutable and retained. Exact source/run/link receipts under /mnt/c/Temp/simple-block-error-span-repair-20261012.

**Revalidated 2026-11-02: still plausible because OPEN; draft source qualification; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-05 compiler-defects sweep (winboot-rel100 lane)
Fix 7847623d84d "fix(blocks): preserve error span source metadata" is an ancestor of release/1.0.0 tip 816655ee5cb; both error_at and error_span in src/compiler/15.blocks/blocks/error_helpers.spl carry `file: ctx.payload_span.file`. Host check (Rust seed interpreter): test/01_unit/compiler/blocks/error_span_native_contract_spec.spl 2/2 PASS. Native fixture (test/fixtures/compiler/block_error_span_native.spl, 8 assertions) remains native-build qualified only. Status: FIXED (host-verified); native producer integration still pending.
