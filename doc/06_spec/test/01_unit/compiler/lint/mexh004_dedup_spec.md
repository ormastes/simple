# MEXH004 Diagnostic Deduplication Specification

Source: `test/01_unit/compiler/lint/mexh004_dedup_spec.spl`

## Contract

Each unreachable match arm emits at most one `MEXH004`, in source order. Query
and semantic lint use the same precedence:

1. duplicate wildcard;
2. arm after an earlier wildcard;
3. duplicate exact pattern.

The query path preserves the offending arm's existing one-based line and JSON
span shape. The semantic warning model remains unchanged. Classification does
not use a post-processing diagnostic set and does not early-return before
coverage or `MEXH006` collection.

## Executable scenarios

The paired executable specs cover duplicate wildcard plus repeated arms after a
wildcard, a duplicate exact pattern before a wildcard, query line ordering, and
equivalent semantic warning order/messages. These scenarios were added but not
executed under the user's no-verification instruction.
