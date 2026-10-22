# Qualified enum method-call constructor ownership

The selected scope is constructor admission in MirLowering.lower_method_call.
The same declaration identity must govern variant membership, runtime ID,
discriminant, and payload-slot metadata. A receiver that evaluates to a value
must retain ordinary method dispatch. A resolved associated function must
retain its authoritative resolution even when its spelling matches a variant.

REQ-QUALIFIED-ENUM-CONSTRUCTOR-001: use enum_constructor_symbol_owner for proven
declaration symbols and enum_variant_index_q for qualified membership, retaining
the same owner through lower_enum_construct_named. Test colliding A.E/B.E,
both registration orders, and0/1/2 payloads with differing declared slot types.

REQ-QUALIFIED-ENUM-CONSTRUCTOR-002: preserve unknown-variant/payload rejection,
associated-function dispatch, and runtime-instance dispatch. Test actual MIR
field projection and function-return evaluation as well as parameter receivers.

REQ-QUALIFIED-ENUM-CONSTRUCTOR-003: retain imported provider identity. The fixture
uses the same define/rename/bind-qualified projection as HIR imports, verifies
the alias lookup and stored author name, and checks actual constructor emission.
Full parsed import qualification is a separate gate, not implied by this probe.

REQ-QUALIFIED-ENUM-CONSTRUCTOR-004: preserve unambiguous lexical bare enum
references. No name is recovered solely from a unique variant leaf on an
arbitrary receiver expression. The inverse registry's maintenance is unchanged.

The test owner is a shared fixture module, called by SSpec and an explicit
native main without BDD initialization. The fixture constructs declaration HIR
through real compiler APIs, begins real MIR functions, invokes the changed
engine, and inspects produced instructions. It never substitutes a toy dispatch
implementation or fabricated MIR success. All assertions use scalar/length
facts; typed-array pointer comparisons are excluded.

Native qualification is NOT_RUN. Importing the full MirLowering coordinator
pulls a larger closure than the seven-object rank probe; its exact selected
module count and whether0CD6 can compile the engine must be established by the
first approved isolated native build. Source inspection alone cannot prove
that bootstrap capability. Use persistent caches and the canonical memory
admission limits; root has reserved up to80GiB with80 requested jobs. An engine
compile failure is a blocked qualification, not permission to replace the
engine with a stub or report PASS. Do not rerun capped whole-stage entries.

After a focused native/API PASS, rebuilding the coordinator and replaying the
actual interpreter provider world remain required before claiming the main
Phase3 fatal is fixed. No Phase3 or full-CLI admission follows from this probe.
