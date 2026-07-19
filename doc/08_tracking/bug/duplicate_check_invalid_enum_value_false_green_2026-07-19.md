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
