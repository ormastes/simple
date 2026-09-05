# Query Diagnostic Severity Override Specification

Source: `test/01_unit/app/cli/query_diagnostic_severity_override_spec.spl`

Evidence status: authored but not executed under the user-requested no-verify
override.

## Scenario: collection preserves exact override semantics

The executable fixture pins zero-override identity, unknown-code identity,
same-severity identity, multi-digit replacement, malformed/missing-severity
fail-closed behavior, and negative override suppression. Each non-suppressed
diagnostic is collected exactly once, and shared state is reset at the boundary.

## Scenario: rewriting avoids byte fragments and intermediate prefixes

The structural fixture requires byte-based digit recognition, a no-digit guard,
a byte-equal unchanged fast path, and one final fragment join. It rejects the
former one-byte substring loop and chained immutable concatenation, while also
pinning strict gate/code/membership/suppression/rewrite/collection order and the
exact nested policy fragment. This makes the no-policy no-scan claim
non-vacuous rather than accepting an unused or unguarded code lookup.

With no active override policy, routing is O(1) before collection/printing and
does not scan diagnostic fields. For N diagnostic bytes, an active policy uses
O(N) fixed-marker scans and O(1) scan state. Unchanged and malformed severities
retain the original text without rewritten output. A changed severity creates
two bounded source slices, one short severity string, and one O(N) joined result;
no runtime allocation, timing, or RSS measurement was performed.
