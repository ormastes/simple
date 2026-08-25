# Query Check Output ANSI Span Specification

Source: `test/01_unit/app/cli/query_check_output_ansi_span_spec.spl`

Evidence status: authored but not executed under the user-requested no-verify
override.

## Scenario: historical cleanup semantics remain exact

The executable fixture pins plain-text identity, normal and consecutive ANSI
escapes, an unterminated escape, Unicode visible text, the mandatory stdout/
stderr newline, and an escape that begins in stdout and terminates in stderr.
The last case proves cleanup still happens after the streams are combined.

## Scenario: output uses one join and visible spans

The structural fixture requires one three-fragment stdout/newline/stderr join
and rejects chained immutable concatenation. ANSI cleanup must find the first
escape, scan ESC and terminating `m` bytes, retain bounded visible spans, and
join once. Per-character iteration and fragment append are rejected.

For N combined bytes, E escape runs, and V visible bytes, cleanup is O(N).
Without ANSI, the joined text is returned without a second O(N) rewrite. With
ANSI, auxiliary output storage beyond the combined input is O(V + E); during
`_clean_check_output`, peak owned output is O(N + V + E). This is span-based,
not zero-copy. No runtime allocation, timing, or RSS measurement was performed.
