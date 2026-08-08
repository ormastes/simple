# Lossless Specification Import to SPipe — TLDR

`spec-to-spipe` is a pure-Simple, lossless import pipeline that considers a
standard converted only when every source byte and applicable requirement is
accounted for and generated tests provide non-vacuous production evidence.

## Contents

- [Pipeline](#pipeline)
- [Core rules](#core-rules)
- [First milestone](#first-milestone)

## Pipeline

Immutable source snapshot -> mapped preprocessing -> lossless syntax tree ->
shared semantic IR -> SPipe/manual/bitfield/diff outputs -> verification ledger.

## Core rules

- Recovery creates source-mapped `ErrorNode`s; it never drops malformed input.
- One manifest pins source, license, adapter, preprocessing, and schema versions.
- Every normative clause has evidence or an explicit blocked/review disposition.
- `spec-to-sspec` delegates to the canonical command.
- Canonical semantics remain pure Simple; bootstrap tools are only oracles.
- Shared contracts freeze before adapters run in parallel.

## First milestone

Prove one Simple Markdown source, one openCypher TCK feature, one RFCXML+ABNF
source, and one CMSIS-SVD+NVMe register input through the same coverage,
source-ledger, non-vacuity, modern-manual, and semantic-diff gates.
