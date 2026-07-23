# Duplicate-check invalid enum value false-green — 2026-07-19

**Status:** SOURCE FIXED / STAGE 4 QUALIFICATION PENDING

## Reproduction

`simple duplicate-check <path> --mode tokne` silently retained the configured
default mode and scanned successfully. Invalid `--format` values likewise fell
through to text output.

## Root cause and fix

The parser validated known option names but not their enum values. Validate
`--mode` and `--format` before scanning, return usage exit 2, and retain both
negative probes in the essential-tools smoke.

## Follow-up: same-file semantic false green

Local semantic mode excluded every candidate pair from the same `.spl` file,
while semantic-LLM mode compared them. The local path now keeps same-file pairs
and still uses its index-based `seen_pairs` key to emit each pair once. The
focused regression uses two documented functions in one temporary file.
