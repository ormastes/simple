# Captured mono verification-use recipe

`mono_archive_verification_use_capture_v1` consumes a real completed execution.
It verifies the actual applied publication ledger again inside its capture scope
before writing any recipe. The retained execution preflight/completion wrappers
now share borrowed checks with that capture; complete coverage, source/provider
authority, feature policy, epoch, ordered roots and the captured publication seal
remain mandatory. No caller report, candidate body selection or cleanliness
digest is an argument.

Capture stores one immutable compact recipe per module, one shared pruning recipe
and an ordered manifest through the existing single raw artifact owner. Every
blob has the existing 8 MiB envelope bound, exact producer/header/key/checksum,
no-follow reads and secure no-replace collision verification. Module recipes
carry original complete archive identity and selected root/FIFO function record
identities. Global metadata retains only unresolved-template exclusions, actually
emitted template names and final counter. The manifest binds exact input authority,
root order, state/applied-ledger seals, epoch and every recipe key/content digest.
The returned pin contains that authority/order/context and immutable manifest
identity; it has no execution/facts owner, HIR, SymbolTable, function or report.

Actual module assembly now delegates to one shared borrowed reassembler. It loads
the original complete module, verifies exact nongeneric root order/coverage, loads
selected complete function records and restores specialization rows/counter. It
uses the existing actual pruning method with compact exclusions/emitted names;
no full monomorphization facts table is needed merely to prune. The actual and
replay record/container keys share one unchanged publication identity codec.

`mono_archive_verification_use_v1` reloads the captured manifest and recipe bytes,
reassembles each exact selected complete body in its own lease, publishes only
assembled metadata, then invokes the actual shared closure-first exhaustive
verifier. The returned report is freshly collected from reconstructed bodies.
The borrowed `mono_archive_verification_use_load_module_in_owned_scope_v1` also
returns only a live complete body inside its parent's active/unpaused lease.
Encoded recipes and scratch bodies are never promoted; result pins/descriptors
and text/scalar reports follow the existing ownership rules.

This is verification-use, not final admission. Public pin constructors and raw
cache bytes are not producer authorization. The genuine driver prerequisite
journal must register the actual returned capture and selected input/stage,
logical/physical order and current epoch before final policy publication or
read-use. Resolved transformed input, original semantic replay, value/layout,
collection and cold-witness prerequisites remain mandatory. No final factory,
final-reader placeholder or activation flag is exported. The existing driver
publisher consumes an actual report only after those real gates.

The independent native `verification` selector requires 18 checks and four exact
fixture files. It does not depend on held candidate patch `a03c98381`. Actual
native cross-module generics return 43; complete reconstructed root/provider
codec digests and all 14 report counters/ordered violations match retained mono.
Replay works after mutable execution descriptors are detached and after second
scope growth. Editing a returned report to a fully clean report cannot become an
input or suppress independently re-collected violations. A well-framed recipe
omitting roots cannot overwrite the immutable captured recipe.

The fixture also changes an actual stored complete function body to return 999,
using the real generated function codec and a valid checksum/header. Raw byte
framing accepts it, but the captured function identity makes body read/use refuse.
The private fixture always restores exact saved bytes before asserting that
control, then requires successful actual replay. Only bounded encoded restore
bytes escape this adversarial fixture lease, never its decoded function. Other
controls reject incomplete capture, changed epoch/order/manifest/cache owner,
inactive/paused reads and nested leases. No native job was started; compilation
and execution remain pending root serialization.

Source dependencies are applied-ledger proof `6409d8aff`, aggregate verifier
`13c3cf6f3`, assembler `b71f0f483`, original borrowed reader `411f2c4`, selected
provider input fields/key `f7c60c79`, single raw cache owner `635fb1200`, complete
records `9e26e7de`, and actual runtime scope-state query `8f87fa0e`. Static source
checks/guards are not native lifetime evidence, original promoted-HIR reclamation
or full CLI RSS qualification.
