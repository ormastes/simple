# Bounded final HIR archive to MIR declaration owner

Status: private implementation draft; production activation and native
qualification are pending. No RSS reduction or full archive-route pass is
claimed. Native/compiler jobs were prohibited while the canonical source was
being built. The authored native and unit fixtures have not been executed.

The legacy MIR route retains every complete provider HirModule. Its provider
consumers require real declaration identities, callable types and effects,
nominal layouts, trait/impl links, defaults, globals and initializer policy.
Dropping bodies from a fake HirModule would change those consumers' semantics.

The new typed declaration roots contain actual SymbolTable ownership, scalar
declaration metadata and field/function type signatures. Ordinary function and
trait-default method bodies have no field in this schema. Parameter defaults,
field defaults, globals and enum discriminants are complete generated-HIR
expression records, addressed by final repository authority, exact final body
digest and declaration/member selectors. Their byte storage uses the one
common borrowed artifact owner; it does not create another cache or infer an
authority from an environment path. The driver selects its actual initialized
producer context before entering scratch.

The intended sequence remains complete final mono admission, declaration
projection in physical representative order, every-module declaration prescan
barrier, one complete final module read in an active owned scope, the original
module construction-site prescan and function lowering, explicit MIR/root
promotion, scope close and reverse-reference publication. Driver diagnostics,
strictness checks, validators, MIR verification and logical source receipts
remain required before activation. The final mono reader/helper and the typed
logical-to-physical receipt are external dependencies, not replaced by this
consumer's shape checks. Logical inventory rows are retained separately.

The provider consumer reuses the existing callable linkage, nominal ownership,
field type, Result Err layout, global binding and initializer policy owners.
Parameter types retain mutability and effects. Static storage uses genuine
decoded demanded initializers and the existing Infer/storage diagnostics.
Layouts use the actual compute_struct_layout result and existing identity
rows. Local declarations still override provider metadata at module entry.
Imported field defaults retain the existing relocation refusal for unsupported
binding scopes. Parameter defaults use a separate complete typed binder, rather
than applying that field refusal to previously supported parameter expressions.
The binder traverses all 60 actual expression variants, 13 patterns and five
statements; lexical declarations are allocated by the consumer SymbolTable,
and earlier parameters alias the actual supplied MIR operands. Function, type
and global references require actual canonical provider declarations. Nested
blocks, lambda parameters and captures retain their metadata and full bodies.
Callable Throws annotations relocate their actual nominal type and keep the
original effect record/span. This source audit is not native equivalence proof.

Lifted default bodies inherit admitted descriptors, callable links and actual
imported initializer metadata. Their lambda registries remain fresh. Actual
child lifted definitions and diagnostics are published with the enclosing
lowering, so a nested closure cannot lose its definition or fatal diagnostic.
The source DTO SymbolTable remains read-only; consumers allocate into the
distinct decoded current-module table. An unbound lexical reference or missing
canonical declaration fails before lowering that default.

Bootstrap function predeclarations can have no defining_module. Foreign
defaults resolve those through the exact retained local function record and
its actual symbol, never through the consumer's current module or a bare name.
Explicit foreign references require canonical provider ownership and an exact
declaration. Repeated references to the same trait/default function record must
encode identically; conflicting declarations fail. The current callable type
comes from retained HirFunction parameters/result/effects, rather than an older
predeclaration SymbolTable type. Its emission name uses the existing actual
declaration link owner. Abstract trait metadata supplies no invented body.

MIR lambda scratch is saved/reset/restored at the actual function emission
boundary. Inline lowering keeps the current function's registry; explicit
child function lowering restores the parent's remembered bindings. The module
archive consumer clears completed module expression scratch before promoting
the lowerer. MIR output still owns its required contracts and spans.

## Native mutable owner boundary

MirLowering is a struct. Native function_lowering.spl binds ordinary struct
parameters to copy_struct_value_recursive's fresh aggregate; its scalar
fields and dictionary replacement therefore do not update the caller.
The copy recursively rebuilds nested value structs and preserves class
references. A shared Dict entry mutation cannot prove scalar writeback.
The archive prepare/lower APIs consequently declare `mut lowering: MirLowering`.
HIR lower_param preserves parser is_mutable, and native function lowering
explicitly bypasses the ordinary-struct copy for that parameter.
The actual LLVM emitter maps MirTypeKind.Struct to `ptr` in
backend/_MirToLlvm/core_codegen.spl:2582. llvm_type_mapper.spl:271-280 sizes
that pointer to target_bits/8. The defensive copy is therefore emitted by
MIR parameter setup, rather than an implicit ABI copy; the explicit-mut
branch receives and writes the exact caller object.

MonoArchiveRegistrationOwnerV1, MonoArchiveExecutionV1 and MonoArchiveStateV1
are classes. MonoArchiveAdmissionV1 is a struct whose state field is that
class. Actual publication modifies the class state, so admission copying
preserves those state writes. No speculative archive owner API rewrite was
made. Existing native archive caller epoch/cursor assertions remain necessary
execution evidence.

Authored coverage:

- mir_archive_owner_writeback: six terminal guards inspect actual MirLowering
  module emission, caller scalar state, dictionary replacement and ordinary
  non-mut struct-copy isolation across real free-function calls.
- lambda_body_owner_lifetime_spec: three actual frontend/HIR/MIR cases cover
  captured lambdas, subsequent named local callables and parent registry
  restoration during explicit child function emission.
- declaration_expression_codec_spec: two actual frontend-generated captured
  lambda cases cover complete legacy codec round trip/binding identities and
  incomplete-record refusal. They do not establish final-stage admission.
- declaration_default_binding_spec: two actual frontend HIR cases inspect fresh
  lexical allocation, preservation of the supplied MIR local, read-only provider
  symbols, and refusal of a missing real provider binder. The fixture deliberately
  has no final archive seals and cannot grant production admission.
- foreign_parameter_defaults: sixteen native terminal guards preserve unchanged
  imported Lambda/Block defaults, earlier-parameter cascades, caller spelling
  collisions, explicit overrides, named functions, text values, runtime global
  initialization, calls with omitted defaults inside a lift, and nested lifted
  definitions, function-valued fields, two distinct trait owners, Float64 slots
  and a real Unit callback's global side effect. It must run
  against both ordinary and activated archive routes. The trait and field cases
  are authored qualification obligations, not native passing evidence.

Static checks confirmed all 18 generated expression/declaration codec
references exist and the new schema/codec/producer files remain below the
800-line source boundary. git diff --check passed. These checks do not replace
native compilation, execution, cache corruption controls or bounded full CLI
qualification against the newly admitted producer/runtime authority.


The follow-up binds callable record names and kinds to the retained table row.
Qualified methods additionally need an actual nominal/trait/impl member edge and
`SymbolTable.method_symbol_name`; matching a suffix does not prove ownership.
The exact local source reference must match that row's name and kind. This also
protects nil-owner bootstrap predeclarations without trusting their stale type:
the actual complete callable record supplies parameters, result and effects.
Before publishing that signature, the binder invokes the existing recursive
`lower_type` diagnostics and `lambda_abi_type_resolved` contract. The added
actual-frontend mechanics cases cover nil-owner/stale-Unit predeclarations,
record-name conflicts, and a nested unresolved inference variable. They are
UNRUN. The current authored total is seven unit cases and sixteen native guards;
there is no native execution, final-route activation, or measured RSS result.


The recursive ABI helper intentionally ignores Function effects. A separate
scoped traversal now visits actual Throws types inside every nested Function,
using `lower_type` diagnostics and the resolved ABI contract on each thrown
type. This preserves effect records while rejecting unavailable provider
nominals even when Error advisories are configured permissively. Two additional
actual-frontend mechanics cases cover a missing nested Throws owner and a real
retained nominal owner. The authored total is nine unit cases, all UNRUN.


The selected foreign field-default artifact reader now uses the same complete
structural binder with an empty supplied-parameter frame. It retains actual
provider lexical, nominal, global and callable owners; Lambda/Block artifacts
no longer go through the limited legacy field relocator. The unchanged ordinary
route remains the control. Native guard17 constructs an imported class while
omitting its typed callable field, then invokes the real captured-global default
and requires12. Seventeen native guards and nine unit cases are authored, UNRUN.


The complete declaration handoff must detach the two body-bearing legacy
parameter-default registry roots before MIR publication promotes global
registries. The selected consumer uses immutable expression descriptors; prior
compatibility HirParam.default rows are not needed there. The narrow detach API
preserves all return/type/link registries and does not run on the ordinary route.
It does not claim reclamation of previously promoted objects. Two actual-frontend
lifetime controls check type metadata survives and ordinary registration remains
usable after detachment. Both are UNRUN. The final orchestration remains a draft
until the genuine driver prerequisite and mono final policy/read owners exist;
no placeholder reader, production activation, or RSS claim is supplied.


The actual lower-level borrowed module consumer now lives in 50.mir without
any driver import. It requires real active/unpaused scope state, installed
complete native declarations, unoccupied lambda/finally scratch, exact retained
module/table declarations, and actual complete encoded body equality. It calls
the existing `lower_module` with no body providers and retains all real MIR
output, errors, advisories and counters. It clears only expression/lambda
scratch and compatibility-default roots after all body consumers finish. It
never begins, pauses, promotes or ends a scope and grants no final admission.
The driver still must supply the body through its genuine final reader and
promote the actual output/diagnostics/reverse-reference batch. Three real
inactive/active/paused lifecycle refusal cases are authored, UNRUN. Successful
final admission and executable semantics remain unqualified, pending the real
final driver and mono owners; no RSS reduction is claimed.


Borrowed lifecycle and positive mechanics specs are tagged `only-compiled`
because their real SFFI scope transitions cannot be qualified by interpreter
stubs. A source-only positive mechanical control projects actual frontend
bytes, installs diagnostic declarations without a final owner, lowers the
complete body, promotes real output/owner/registries, closes the scope, and
requires its actual typed return operand to contain7. A paired case changes the
actual HIR tail to8 and requires refusal while leaving the caller's scope active.
The diagnostic identity explicitly grants no final policy/prerequisite admission.
These two cases, the three lifecycle refusals, and all actual native controls
remain UNRUN; emitted MIR graph checks do not qualify executable semantics.


The post-HIR borrowed fact readers previously used current parser registry
claim counts to select effect size/name measurement, effect body walks, RT
graph extraction and forward join points. Replaying an actual archive after
registry reset could silently lose captured policy validation inputs. Shared
selected readers now accept explicit effect/aspect/RT selection flags. The real
immutable policy owner must derive flags from actual captured claims; the flags
themselves grant no admission. Ordinary wrappers retain current selection and
original scope refusals. Global/local HAL declarations still activate the full
RT graph with RT selection false. Layer last-name winner traversal and complete
body/archive/warning custody are unchanged. No-claim selection still excludes
effect layout measurement; value/layout validation retains its original route.

The managed parse/archive fixture extends14 to26 checks: explicit flags false
with populated registries, real registry reset, preserved transitive24-byte
effect diagnostics/RT allocation graphs/forward identities with captured
selection, and ordinary wrappers following the new empty state. A genuinely
parsed and archived HAL source tests global/local HAL activation with flags
false. Warning/body identity and scope closure remain checked. All26 native
controls are UNRUN. There is no final/executable/RSS qualification claim.
