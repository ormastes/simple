# Cranelift imported-global address ABI v1

Status: public-only accessor correction verified by a native helper/object
probe; full adapter gates await an updated combined producer. This is not
merge admission. Earlier construction timeouts remain in the tracking report.

Scope: pure-Simple Cranelift object generation. This is an internal compiler
ABI implemented using existing function/data SFFI operations, not a new runtime
API. No Rust or C implementation changes are required.

## Ownership and representation

Each provider defines its global's data exactly once using the existing
owner-qualified storage identity. For public data only, it defines a zero-argument
address accessor named `__simple$global_address$v1$<storage-identity>`.
The dollar-delimited prefix is outside the source identifier namespace;
the full existing storage identity is retained, with no new hash truncation.
Public accessors are exported. Private and scoped data receive no accessor;
their local uses retain direct data addressing and existing data linkage.
The native AOT function-definition API always redeclares functions as Export,
so requesting Local or Hidden does not preserve either visibility. The helper
rejects every non-Export request before native calls.

The accessor returns Cranelift `CL_TYPE_PTR`, so its calling convention and
return width follow the target rather than a host-process pointer assumption.
Its body obtains the address through Cranelift's data relocation API. No
compiler-process addresses or fabricated initial values enter the target.

A consumer of public data declares only an imported accessor function. Its MIR `LoadGlobal`,
`StoreGlobal`, and `GlobalAddr` operations call that accessor and use the
returned provider address. The consumer never declares or defines global data.
An external non-public static is an explicit unsupported-backend diagnostic:
`requires visibility-preserving accessor support`. This is not a change to
language visibility. Legal package/sibling access exists (for example
`test/fixtures/compiler/imported_globals` imports `pub(package) SCOPED_VALUE`),
but cannot use this accessor ABI until the provider preserves scoped linkage.
`CraneliftGlobalBinding` has separate data/accessor handle fields; exactly one
is populated, and invalid bindings fail instead of being interpreted as data.

Existing MIR provider-initialization calls precede imported reads, writes,
and address taking. The accessor itself does not initialize or copy storage.
The existing guarded initializer owns the once-only state and dependency
ordering. Thus repeated consumer reads or writes cannot reset provider state.

## Inline-only constants

The provider intentionally emits no storage for private immutable scalar
literals. Import registration transfers their exact folded literal value and
retains the provider-initializer dependency. It never evaluates a foreign
expression with consumer SymbolIds, inlines a mutable/public binding, or
invents a zero. Interpolated text and compound expressions keep their storage
and runtime-initialization routes.

Taking an address of an imported inline-only private constant is rejected
explicitly: the consumer cannot manufacture provider storage. Public and
otherwise addressable globals retain their existing external static binding
and use the accessor route.

## Cost and boundaries

Static declaration remains one linear pass over the current module. There are
no new source scans, shell-outs, polling, or runtime module searches. Imported
global accesses incur one additional direct function call; local accesses
continue to use direct data handles. Providers emit one small accessor per
public stored global. No cache invalidation policy changes are introduced; ordinary
source/compiler identity invalidation applies.

This version requires Cranelift-generated providers for Cranelift consumers.
Mixed-backend linking requires the same accessor ABI from the other provider
or a future declaration-only native data API; it is not implied by successful
same-backend object generation. Unsupported static types and payloads remain
explicit failures.

## Executable gate

`test/fixtures/compiler/native_imported_global_storage` has a provider and two
consumers. Its main program checks initial state, consumer-to-provider writes,
provider-to-consumer writes, both consumers observing the same value, exactly
one initializer execution, and the actual private literal value. Its
`private_address.spl` entry must fail with the explicit no-provider-storage
diagnostic. ELF symbol inspection must show one owner data definition and
consumer accessor imports, never consumer data definitions.

`native_cranelift_accessor_visibility.spl` supplies real AOT/data handles and
requires Local, Hidden, and Import accessor-definition requests to fail. It
emits a public accessor object for ELF symbol inspection; no rejected accessor
symbol may appear. `native_imported_global_storage/scoped_import.spl` must fail
with the explicit unsupported-visibility diagnostic, while the provider's own
private and scoped accesses remain compilable without exported accessors.

Verification evidence is recorded separately; this design does not itself
claim compiler, MCP, release, or mixed-backend admission.
