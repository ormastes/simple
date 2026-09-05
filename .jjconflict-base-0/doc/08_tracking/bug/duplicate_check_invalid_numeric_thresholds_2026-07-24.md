# Duplicate-check accepted invalid numeric thresholds

Status: SOURCE-FIXED; fresh pure-Simple runtime qualification remains pending.

## Bug

Equals-form values such as `--min-tokens=-1` passed CLI preflight and reached
the detector as invalid token-window sizes. Malformed integer text could also
reach unchecked `int(...)` conversion. Configuration files had the same missing
range checks. Malformed floating threshold text had the same unchecked path.

## Root fix

The canonical configuration validator now requires positive `min-tokens` and
`min-lines`, plus nonnegative `min-impact` and `max-allowed`. CLI target
preflight also requires integer or floating syntax before conversion. The
focused contract covers direct configuration, equals-form ranges, and malformed
numeric text.

## Remaining qualification

Run the focused threshold contract once through the next fresh incremental
Stage 4 CLI. Temporary seed or stale-binary results do not qualify production.
