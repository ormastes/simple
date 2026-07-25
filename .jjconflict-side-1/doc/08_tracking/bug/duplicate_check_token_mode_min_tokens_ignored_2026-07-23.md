# Duplicate-check token mode ignored `min_tokens` — 2026-07-23

**Status:** SOURCE FIXED / PURE-SIMPLE QUALIFICATION PENDING

## Reproduction

Token mode reported identical `min_lines` windows even when their actual token
count was below `--min-tokens`. It also labeled each block with the configured
minimum instead of its measured token count.

The regression in
`test/01_unit/app/duplicate_check/detector_grouping_spec.spl` duplicates a short
function across two files, sets `min_tokens = 100`, and requires zero groups.

## Root cause and fix

`fast_line_window_duplicate_groups` only checked signal lines and copied
`config.min_tokens` into each result. The shared line-prefix pass now records
actual token counts; token-mode windows must meet the configured minimum and
report the measured count.

The threshold regression passed through the temporary Rust bootstrap
interpreter, which also measured 22 tokens for the retained-count assertion.
A fresh pure-Simple Stage 4 candidate must run the complete focused spec before
qualification.
