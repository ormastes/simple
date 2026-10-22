# Qualified enum constructor dispatch loses declaration ownership

BUG-QUALIFIED-ENUM-CTOR-OWNER-20261016. Database entry pending: no bug database
tool available. Diagnostic candidate only; native qualification NOT_RUN.

The frozen C1 Phase3 cohort's first prefix-proven fatal pair is `undefined
variable Value` / `unresolved method call: Bool` in backend/interpreter.spl
(stderr42323–42324). Value is declared and exported by the tier-root
backend_types.spl, and the interpreter imports that owner. The retained error
rows are module aggregates, without the actual receiver owner; they do not
prove all89 undefined-Value messages share one cause.

The C1 method dispatcher recovers a qualified type-valued receiver and then
checks the bare enum registry. Remote2cff addresses the miss by collapsing the
owner to the last-wins bare key, which can instead select a sibling enum's
runtime ID, discriminant, or payload metadata.

The repair admits a declared enum through its exact qualified registry and
passes that same owner to lower_enum_construct_named. Resolved associated
methods retain their existing dispatch. Parameters, fields, and call results
cannot become static constructors merely because a variant name exists. Legacy
bare recovery requires the lexical receiver name itself to name an unambiguous
registered enum; variant-leaf uniqueness alone is not type-valued proof.
No inverse-index maintenance, payload ABI, or broader enum guards change.

Imported enums use SymbolKind.Enum and the provider's defining_module. HIR
import registration defines the lexical alias, then renames the stored symbol
to the author's original enum name while retaining the alias lookup key. The
fixture exercises these actual SymbolTable APIs; it does not claim full
multi-module import parsing or actual-C1 replay qualification.

The native fixture compiles the changed MirLowering implementation into its
entry and calls real lower_method_call. It inspects emitted enum IDs,
discriminants, tuple allocations/stores, and real diagnostics for two colliding
E declarations, both registration orders,0/1/2 payloads, invalid payloads,
missing variants, runtime parameter/field/call receivers, associated methods,
import alias projection, and legacy unique bare references. Expected negative
lowering diagnostics may print; an exit0 must still satisfy every fact check.
No runtime PASS or new-producer admission is asserted by source existence.
