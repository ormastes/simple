# Generic producer optional-binding candidate

STATUS: UNQUALIFIED; executable specifications and native fixture are UNRUN.

When a generic producer returns T?, HIR can retain a symbolic Optional<T> on
ExistsCheck and a symbolic T on the if-val binding symbol. Concrete-only symbol
selection cannot use that evidence yet. Falling back to the optional initializer
would specialize a payload use as Optional<text> rather than text.

The collector now asks a dedicated helper to establish the original binding
relation. Shared HIR structural equality distinguishes the binding's
symbolic type from the original Optional payload and from the whole Optional.
The comparison uses retained semantic types from the same HIR binding context;
it is not display-name matching or equality of ids from unrelated module tables.
Symbolic evidence admits concrete leaves and formal type parameters, but rejects
Any, Error and Infer holes. Effect-bearing function subterms are also rejected
on both sides because the shared comparator does not compare effects; no global equality
semantics changes. The helper then infers the producer's concrete
Optional result and selects either its payload or its whole type according to
the proven relation. Exactly one Optional layer is removed for a payload binding.

If original evidence is missing, erased or mismatched, the binding remains
uninferred and a dependent generic call reports E-MONO-032. General initializers
retain their previous inference path. No HIR schema/cache layout, runtime
representation, global symbol types or MIR sentinel behavior is changed.

Regressions cover different formal parameter names, nested Optional payloads,
ordinary whole-Optional bindings, erased/missing evidence refusal and a parsed
generic-producer if-val case. Native fixture `generic_if_val_producer` covers
text/integer payload calls, absence and an ordinary optional value binding.
Expected stdout is `text=ab int=5 absent=none ordinary=z`; native LLVM and runtime
qualification remain required.

Remaining legitimate gap: producers whose HIR signature or imported surface
does not retain this relation require better semantic provenance. They must not
be silently unwrapped. This candidate is not a completed-generics declaration.
Symbolic payloads containing effect-bearing functions remain unsupported until
their effect relation has a verified comparison; the tests cover both symmetric
and asymmetric effect-bearing evidence.

Independent source review found and resolved the asymmetric effect comparison
gap, then reported no remaining demonstrated P0/P1 in this scoped patch. Staged
whitespace, working/staged runtime-facade guards and numbered-artifact guard
passed. These source checks do not replace executable qualification.
