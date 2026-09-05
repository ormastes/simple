# Standalone Target Build Without Bootstrap

## Purpose

This operator contract keeps independently shipped products, beginning with
Office, separate from compiler bootstrap.

## Preconditions

- An executable absolute Phase 3 compiler path is available.
- The adjacent `provenance.env` passes the canonical Phase 3 verifier for the
  current repository root.
- Product cache and output are outside `build/bootstrap/`.

## Procedure

1. Set `SIMPLE_TARGET_PHASE3` to the admitted compiler.
2. Run `sh scripts/check/build-office-standalone-target.shs`.
3. Confirm the receipt records compiler digest, output, and cache.

## Safety Properties

- The wrapper invokes no Stage 1, Stage 2, or Stage 3 bootstrap.
- It sets `SIMPLE_NO_STUB_FALLBACK=1` and
  `SIMPLE_STRICT_FABRICATED_STUB_RATCHET=1`.
- Missing, stale, symlinked, seed, or unreceipted compiler input fails.
- A product result is not Stage 4 deployment, SPipe execution, or release
  evidence.

## Focused Contract Check

```bash
sh scripts/check/build-office-standalone-target.shs --self-test
```
