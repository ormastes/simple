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
