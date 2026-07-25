# Duplicate-check accepted impossible similarity thresholds — 2026-07-23

**Status:** SOURCE FIXED / PURE-SIMPLE QUALIFICATION PENDING

## Reproduction

`simple duplicate-check <path> --semantic-threshold 2` reached comparison with
a threshold above the maximum cosine score. It could suppress every match and
exit 0 instead of reporting invalid usage.

## Root cause and fix

Configuration validation covered mode and output-format enums but not numeric
probability bounds. Similarity, semantic, and semantic-drift thresholds now
reject values outside inclusive `0..1`, including NaN, before scanning.

The focused contract covers configuration fields plus split and equals CLI
forms. A fresh pure-Simple Stage 4 CLI must run it before qualification.
