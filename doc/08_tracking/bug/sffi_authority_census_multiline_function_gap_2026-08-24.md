# SFFI authority census skips multiline function bodies

**Status:** Resolved

## Evidence

`cl_translate_instruction` in
`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` has a multiline
signature and calls `rt_env_get` inside a lexical `unsafe(ffi)` block. The full
authority row table omits that call, while it correctly includes the same
symbol inside the later one-line `cl_function_emit_name` function.

The scanner starts body traversal immediately after the first `fn ...(` line.
It then sees the signature-closing `):` at the function's indentation and
mistakes it for the next top-level statement, terminating before the body.

## Required repair

Parse or conservatively scan through the complete function signature before
applying body indentation rules. Preserve line numbers, block-form unsafe scope
tracking, prose masking, and the single O(source bytes + call sites) tree pass.

## Acceptance

1. The Cranelift unsupported-MIR `rt_env_get` call appears exactly once as
   `lexical_unsafe`.
2. Existing one-line function rows remain unchanged.
3. Multiline declarations without a body do not absorb the following function.
4. The selftest covers multiline `fn` and `me` signatures plus nested unsafe
   blocks.

## Resolution

The scanner now advances through a bounded complete signature before applying
body indentation, with a zero-lookahead fast path for ordinary one-line
headers. The selftest covers multiline functions, methods, lexical unsafe
blocks, and a multiline extern followed by a separate function. The corrected
full scan includes the Cranelift unsupported-MIR call as `lexical_unsafe`.

Performance acceptance remains separate and open in
`sffi_authority_multiline_scan_perf_regression_2026-08-24.md`.
