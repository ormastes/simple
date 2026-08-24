# MEXH004 Diagnostic Deduplication Specification

Source: `test/01_unit/compiler/lint/mexh004_dedup_spec.spl`

## Contract

Each unreachable match arm emits at most one `MEXH004`, in source order. Query
and semantic lint use the same precedence:

1. duplicate wildcard;
2. arm after an earlier wildcard;
3. duplicate exact pattern.

The query path uses the first real arm's indentation as the sibling-arm
boundary. Blank/comment lines and deeper multiline body statements—including
nested `case` text—cannot mutate wildcard, pattern, or arm-count state.
Diagnostics preserve one-based lines and now span the actual indented arm or
match token rather than starting at column 1. Text output and the semantic
warning model remain unchanged. Classification does not use a post-processing
diagnostic set and does not early-return before coverage or `MEXH006`
collection.

## Executable scenarios

The paired executable specs cover duplicate wildcard plus repeated arms after a
wildcard, a duplicate exact pattern before a wildcard, query line ordering, and
equivalent semantic warning order/messages. They additionally cover multiline
wildcard bodies, nested case text, later sibling detection, and exact indented
arm/match JSON columns. These scenarios were added but not executed under the
user's no-verification instruction.
