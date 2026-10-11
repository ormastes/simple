# Phase2 native byte membership in the escaped-size predicate

Status: OPEN compiler/type-lowering investigation; local size predicate corrected.
Owner: compiler/native lowering. Observed during the graph codec acceptance lane.

The original shared size helper used
`[92, 34, 10, 9, 13].contains(s.byte_at(index))` to charge escaped bytes.
The native diagnostic for input bytes `[120,92,34,10,9,13]` reported predicted
size8 while the actual shared writer emitted13 bytes. None of the five escape
bytes were charged. Ordinary text, numeric-looking strings, colon IDs and Unicode
had matching predictions in the same diagnostic. This is a concrete failed
compact-expression observation, not a proven general Array.contains root cause.
Distinguish numeric boxing, argument-expression lowering and inferred element
types before changing the compiler; no compiler fix is claimed here.

The size helper now binds the byte and uses explicit numeric comparisons for
backslash, quote, LF, tab and CR. The final native graph SSpec checks exact shared
writer lengths for ten spelling classes, including all five escape characters,
and passes14/0. This corrects graph sizing, not the open language investigation.

Retained diagnostic: `build/native_probe/traceability-graph-size-diagnostic-20261011/observations.log`.
Native construction used the authorized Rust bootstrap; execution used the
produced Phase2 native artifact. Host hashes live in the graph evidence record;
they are not an authenticated compiler or SPipe admission receipt.
