# Core evaluator array value boundaries and copy on write

Status: source repair and regressions authored; execution and producer
qualification pending. W2 topology caching remains held. This report is not an
array capability receipt and does not qualify the MIR interpreter, JIT or native
backend.

## Observed source defect

At source baseline `44b513f1483f2ec2ee52d353b7b7c53f2746524c`, core evaluator
local binding and function/method return use `val_copy_if_value_struct`, which
returns array ValueIds unchanged. Identifier reassignment and several insertion
paths also store the original ValueId. Index and array-method mutation then
modify that same guest array. Thus `var copy = source; copy[0] = 9` changes the
source, and an array getter can expose stored children. Existing parameter
copying recursively clones arrays, avoiding aliases at an unconditional linear
cost. Both conflict with the array value ABI contract, sections 3.1 and 3.2.

These are source-proven paths; no failing admitted-runtime reproduction has
been executed in this lane. Raw MIR `Copy` is not changed: source MIR lowering
already inserts array value-copy operations, and a raw instruction also moves
temporaries and joins. Its safety requires a separate actual source-to-MIR
execution.

## Repair and invariants

The value owner separates guest array descriptors from backing rows. An array
value boundary allocates one descriptor and increments the backing reference
count, without visiting elements. Scalar length/index readers avoid returning a
host row for these operations. The first shared writer copies its row, forking
direct child-array descriptors; further writes to an unshared row reuse it.
Clear installs empty storage directly and never copies discarded elements.

Frozen value places evaluate receivers and keys once. Mutable traversal detaches
array ancestors and lazily copies/rebinds value-struct children; classes retain
their reference identity. Sparse child ownership stamps avoid copying a struct
and its field arrays on every subsequent write. Ordinary snapshot forks
invalidate stamps in constant time. Internal read traversal leases preserve
stamps, snapshot escaping value children, and release their descriptor on every
return, including errors. Callback mutation still sees a shared row and detaches
the writer.

Incoming values are snapshotted before resolving/writing the target, including
self insertion. Final-index callbacks run before ancestor detachment, so a
snapshot taken by an index callback remains isolated. Bindings, reassignment,
return, constructor/default/spread fields, container insertion, iteration,
pattern binding and forced lazy values use the shared value gate. Spread fields
are captured before evaluating later arguments. Class fields that contain
arrays hold array values; class-valued elements remain references.

Call arguments are captured in source order. Nonmutable arguments snapshot
before later argument effects; declared mutable arguments borrow frozen places.
Only declared mutable whole replacements write back. Both same-place prefixes
and identical array descriptors through different roots reject simultaneous
mut/value aliasing before the callee body. This is a core runtime guard, not
the ABI's desired compile-time alias diagnostic. Non-place mutable array inputs
are rejected before the body. Nonmutable value-struct method receivers snapshot
before arguments; class receivers retain identity.

The value arena owns child identities. Releasing a backing never recursively
frees children. Recycled descriptors release their backing and clear the mapping;
reset clears all backing/refcount/stamp state. Guest scope/result descriptors
are conservatively retained until arena reset; this is not general garbage
collection. Such retained snapshots can conservatively trigger detachment.
Temporary read-method leases are explicitly released to avoid an at/read then
write loop copying the entire row repeatedly. Epoch overflow clears sparse
stamps once; normal fork cost is constant in array length.

## Authored evidence

`test/01_unit/compiler/interpreter/core_array_cow_spec.spl` invokes the real core
pipeline using `core_jit_interpret(..., 999999)`, whose canonical initializer
disables JIT. It checks bidirectional local/global aliases, forced lazy binding,
constructor/getter/default/spread snapshots, nested arrays/structs, class
identity, insertion/self insertion, mutable argument replacement and alias
rejection, argument/index/receiver effects, ordinary missing-key reads, iteration,
and the actual ExprStoreState getter/take/install surface.
The CE binding control explicitly invokes its parsed declaration and asserts a
body-effect counter: current `eval_module` skips top-level `DECL_CE`, a separate
pre-existing execution gap. This repair does not add CE module dispatch or claim
that an automatically executed top-level CE block passed.

Deterministic owner controls check: read-only fork/length creates one descriptor
and zero backing copies; first shared mutation copies one 4096-element row;
subsequent unshared write and shared clear copy no additional rows; repeated
at/write does not retain traversal leases; readonly contains does not invalidate
owned struct children; callback mutation retains the original traversal and
escaping nested children stay isolated after lease release; method errors release
the lease before a subsequent owner write; recycling preserves live backing and
child identities.
Counters describe this owner and are not engine capability proofs.

`test/fixtures/compiler/core_array_cow/main.spl` executes nineteen standalone
cases from `cases.spl`, checks all results, and reports the case count.
`expr_store_state.spl` exercises actual compiler arena APIs and fails closed if
the selected configuration does not expose the real argument column. Its
constructor, getter and installed-state nested snapshots must remain isolated.
The former raw-array-pool source pin in `pure_interp_owner_mutation_spec.spl` is
replaced with owner behavior. The internal Copier fixture now declares its
mutable output parameter explicitly.

## Verification boundary and next admission

### PR 7664 read-parity correction

The initial candidate classified field places by whether their root name was
bound in the environment. That changed existing read precedence: declaring an
enum `State` with variant `State` binds that name as a global value, but ordinary
`State.End` still resolves the known enum variant first. Value arguments and
method receivers must preserve the same precedence. The live field reader and
place preparation now share its canonical special-field dispatch (BDD,
namespace, enum, static function and deferred lookup). A special result is a
value root, rather than a writable storage path, and each dispatch/base
expression executes once. Text indexing in places uses the original `s[index]`
expression; no slice/index Unicode equivalence is assumed.

Parsed controls compare direct reads with argument and receiver reads for the
bound enum-name collision, registered static function references and non-ASCII
text indices. Index callbacks assert once-only evaluation. Mutable struct and
class receiver controls pass the receiver's own array field by value, mutate
both sides in the method, and assert isolation. Such receiver fields are not
part of the explicit argument overlap guard: safety comes from capturing value
arguments before mutable receiver resolution and the array ownership gates.
This does not claim a compile-time receiver/argument alias diagnostic.

A targeted owned `.spl` consumer audit across `src` and `test` found no remaining
`val_arrays` references after replacing the one external raw array write and its
obsolete source pin. This is source ownership evidence, not execution evidence.

Only source inspection and whitespace checking have run. No Simple lint/check,
SSpec, standalone fixture, native smoke or performance execution has run. No
Rust seed is an eligible substitute. The sole bootstrap owner must supply an
admitted self-hosted producer, Hello receipt, exact source/runtime/backend/target
and isolated execution/cache slot before these tests run. Record real assertion
counts, exits and artifacts then; a linked candidate alone is insufficient.

No caller flag, environment toggle, `rt_is_interpreter_runtime`, hardcoded
capability success or universal-false capability stub is added. W2 admission
needs an actual executing-engine/producer-bound capability after qualification,
with producer changes invalidating proofs. JIT/native/MIR behavior, compile-time
mut/value alias diagnosis and general arena reclamation remain separately
unqualified. Existing compiler/core/lib/MCP smoke requirements remain pending.
