# Class declaration ownership across HIR and MIR

The canonical key is the defining module plus the declaration's source name.
Lexical aliases live in scope bindings and do not allocate a second identity.
The owner normalizer shares path/drive sanitization with the common module
path service, then folds numeric tiers and the std/lib alias consistently.

HIR allocates classes by qualified owner/name before binding local spellings.
Class and impl scopes bind their owning declaration so a same-spelled outer
import cannot redirect constructor references or Self ownership.

MIR's provider_metadata module relocates a provider Named/DynTrait symbol by
owner/name into the active SymbolTable. It recursively rebuilds type containers
and supported default expressions. Allocation uses consumer IDs; a foreign
numeric ID is only read against the provider table. Existing qualified bindings
cache repeated relocation. The flat table builder preserves source IDs only
within that source table and rebuilds the allocation counter and indexes.

The flat bootstrap path visits every provider class before active type
registration. Ordinary module lowering borrows the driver's provider array
after installing the consumer SymbolTable. Neither path retains a provider
table per class or field. Canonical class keys are authoritative; provider and
consumer raw composite_layout_key spellings remain compatibility aliases.
Only the active module publishes its bare class spelling.

Default relocation supports literals/interpolation, calls, constructors,
resolved and unresolved method calls, field/index access, basic operators,
arrays/tuples/dictionaries, and casts. Captures, module global reads, lexical
blocks and other unsupported shapes become Error nodes. Errors propagate to
the default root during relocation and are diagnosed when an omitted field
uses that default. They must never reach the old zero-fill fallback.

Callable linkage is recorded from defining HirFunction metadata, because a
HirSymbol alone does not carry export/extern/global attributes. The resulting
owner/name-to-link map drives definitions, operands, and function values.
Export aliases remain the backend export-map's responsibility. A helper named
main is qualified unless its module is the actual entry or it has @entry.

Global return-type caches accept only types without module-local IDs.
Consumer-local function signatures precede those caches. Class return and
Option/Result payload provenance uses canonical class names.

The retained field/default/type maps already participate in MIR transient-root
promotion. The new callable link map is included in that inventory; its flat
bootstrap registry also participates in bootstrap registry promotion/reset.

Qualification and cache probes cost O(owner-name length) plus a dictionary
probe. Default relocation is linear in expression size and happens during
metadata preparation, not at each constructor. Flat provider-table rebuilding
still costs O(provider symbols) per consumer module containing cross-module
classes. Its elapsed-time/RSS impact is unmeasured until an admitted self-hosted
runtime is available; no performance acceptance is claimed.
