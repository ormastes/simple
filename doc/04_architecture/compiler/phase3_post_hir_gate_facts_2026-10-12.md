# Shared post-HIR gates and diagnostic routing

`driver_hir_post_validation_gate_facts_v1` runs the existing explicit-claim
validators on actual complete-body facts and captured policy. It returns the
full ordered errors, warnings, census messages, aspect errors, layout counters
and ordered forward-weave recipe. These public inputs and reports are
mechanics; the compilation owner must independently collect them from the
actual ordered source bodies and bind the captured source/policy owner.

The gate order remains value-struct layout, aggregate census, layer equivalence,
effects, RT criticality and aspects. Only cycle diagnostics can be downgraded
by the captured layout policy; internal layout errors remain fatal. A partial
census loss prints the existing bounded evidence and skips the remaining gates.
When the predicate rejects every entry it retains the original warning and
unguarded continuation. The real driver supplies that actual census result;
a caller-provided count is not authority to accept an archive.

RT diagnostics retain their existing typed order and warning/error severity.
The explicit route reads the captured pre-consumption capabilities and compiled
severity policy, and never consumes, clears or installs the ambient manifest.
The retained driver still invokes the original consuming RT validator once at
the same sub-pass and delegates only its diagnostic routing to the shared leaf.

The retained route also delegates layout filtering, census messages and the
ten-message fatal printer to the same leaf. It keeps the actual Dict census,
live validators and complete-body weaver. Its profiling receipts and emitted
warning/fatal strings remain at their original phase boundaries.

On archive capture, intermediate warnings and census messages are emitted at
the same gate points. Synchronous verification replay can set
`publish_intermediate=false`; this suppresses logging only and still runs every
validator. The resulting typed transcript must match the captured transcript.
The engine must perform actual claim-major weaving whenever aspects have no
errors and the census did not skip gates, even when an earlier gate failed.
It must then call the shared fatal printer, preserving the retained
weave-before-final-fatal order. A recipe does not prove that rewriting occurred.

Native controls and full production-owner integration remain pending. Source
review and this extraction do not admit a compiler, final repository or MIR
reader, and establish no RSS improvement.
