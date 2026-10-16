# Qualified enum constructor dispatch detail

1. Keep the existing static declaration recovery. Only an unresolved call can
   be reclassified; authoritative static/instance resolutions keep their paths.
2. Resolve an enum declaration through enum_constructor_symbol_owner. Never
   strip a qualified key to its leaf. If exact metadata is unavailable, do not
   substitute another enum with the same bare name.
3. A receiver without a declaration may use the legacy path only when its
   lexical NamedVar spelling names an unambiguous registered enum. Fields,
   computed calls, and runtime declaration symbols fail this admission check.
4. Read variant membership from the qualified map when available, otherwise
   the admitted legacy bare map. Pass the unchanged owner to the existing
   constructor, which checks declared payload arity/types and emits the runtime
   construction. No payload layout/transport algorithm changes.

The native fixture uses A.E ordered Zero/One/Two with integer and integer/bool
slots, and B.E ordered Two/Zero/One with bool and bool/integer slots. Expected
discriminants follow those authored orders. Runtime IDs come from real enum
registration; they must differ, and each actual emitted call must use the
selected declaration's ID. Two-field constructions must actually allocate and
store two tuple slots. A wrong-slot argument must reject before enum emission.

The first native command must compile the engine source as a dependency of
qualified_enum_constructor_native.spl. Building an ordinary constructor user
under unchanged0CD6 would exercise old producer behavior and cannot qualify this
implementation. Preserve exact source/producer/runtime identities and inspect
the generated object symbols to prove the changed method is present. Require
clean linking and parent review before running the native entry once.

Existing real negative lowering paths may emit their diagnostic notices. The
control's nonzero failure codes and named checks determine success; no blanket
stderr suppression or diagnostic clearing is permitted. All build, execution,
and broader runtime gates are currently UNRUN.
