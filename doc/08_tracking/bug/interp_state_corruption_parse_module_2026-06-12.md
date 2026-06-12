# Interpreter state corruption around interpreted parse_module (hex-literal conversion)

- **ID:** interp_state_corruption_parse_module
- **Severity:** P2
- **Date:** 2026-06-12
- **Component:** Rust seed interpreter (`src/compiler_rust`), interpreted execution of the lean frontend
- **Status:** OPEN (workarounds in harnesses; root cause in seed not investigated per fix-.spl-first rule)

## Symptom

`error: semantic: cannot parse 'f' as i64` — the interpreted lean parser dies
converting a hex literal (`0xff` in `src/lib/bitwise_utils.spl:8`) when, and
only when, specific interpreter constructs precede/surround the
`parse_module()` call. The identical parse at top level of `main()` succeeds.

## Repros (both minimal, probed 2026-06-12)

1. **for-in iteration**: calling `parse_module(src, path)` inside
   `for fpath in [...]:` (array literal or split() result) crashes; the same
   calls in an index-`while` loop succeed. Repro: `tmp/site12/loop_repro.spl`.
   Wrapping the parse in a helper fn does NOT help — it is the for-in frame.
2. **fs write before parse**: `file_write_text(...)` executed before
   `parse_module(...)` poisons the next parse identically, even inside a
   `while` loop with a hardcoded path. Repro: `tmp/site12/loop_matrix.spl`
   (case A).

## Hypothesis

Some interpreter-global channel (likely the `SIMPLE_BOOTSTRAP_CORE_TOKEN_TEXT`
env-var token-text transport, or a shared string buffer) is clobbered by
for-in frames and by the fs-write extern path, so the number scanner's token
text gets replaced/truncated and the IntLit conversion sees a hex digit.

## Workarounds (active in sweep harnesses)

- Iterate with index-`while`, never for-in, around interpreted `parse_module`.
- No `file_write_text` calls interleaved with parses; buffer results in memory
  and write once after the loop. See `tmp/site12/lean_parse_sweep.spl` header.
