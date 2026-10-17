# Open: native conditional cross-trait casts lose receiver ownership

**Status: OPEN; no implementation or runtime PASS.** This is separate from the
nested-field Result type-query repair. No trait vtable, runtime ABI, cast or
buffer application source is changed in that repair.

The actual frozen `3636b716294` smux diagnostic build under the Hello-qualified
f612 producer completed HIR for 117 modules, then failed MIR in four modules.
`build/smux-diagnostic-current/smux-build.stderr.log` in
`D:/dev/simple-smux-upstream-20261017` records sync buffer unresolved close/is_open
at lines 236/243 and 375/382, with corresponding AsyncClose failures in async
buffer code. Receivers are the if-val binders of `self.inner as Close` and
`self.inner as AsyncClose`; the source's declared trait method signatures exist.

Source-supported mechanism: `lower_cast_or_convert` performs a generic MIR cast
outside numeric/text handling. It does not query whether an erased source trait
value implements the destination trait, rebox using the destination vtable or
preserve Optional<destination trait> provenance. `enum_match_expr_type` lacks a
Cast arm. The if-val payload path can preserve a trait owner only when its input
already has the precise optional-trait type, so the binder's method dispatch
cannot select the intended owner. Merely adding a type label is insufficient:
the inspected native table contains a copy thunk, reference-semantics flag and
trait-specific method slots, without the required dynamic cross-trait query.
Read and Close slots cannot safely be reinterpreted as one another.

The f612 and current `8617a98e315` cast-lowering method bodies are identical at
this boundary. No claim is made that a newer producer already fixes the cast.
No identical failing build was rerun for this report.

Required owner work: establish canonical concrete identity/capability query
metadata, emit actual successful destination-trait reboxing and nil on absent
capability, retain ownership/copy/reference policy, then propagate the exact
optional destination type through the cast and if-val binder. A precise
unsupported diagnostic is preferable to an unsafe bitcast while implementation
is absent; such a diagnostic is not feature completion.

Required runtime coverage: dual Read+Close implementation with observable close
and is_open effects; Read-only negative cast selecting else without effects;
two concrete implementations dispatching different methods; field-held erased
trait values; AsyncClose signature preservation; and copy/drop/ownership
behavior. Unique-implementor guesses, hardcoded success, source-shape checks or
buffer-side grammar workarounds cannot satisfy these gates.

Provider input/output/cache-read/cache-create usage, comparable cohort average
and ratio: unavailable, not guessed.
