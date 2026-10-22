# Imported fixed extern authority

Authored 2026-10-03; seven scenarios, unexecuted. The fixtures parse separate
provider and consumer modules through the real module-surface import machinery.

Selective and aliased imports must retain exact pointer/i32 or zero-argument
pointer signatures in MIR and LLVM, using the physical extern link name. A
same-shaped ordinary function must not gain extern authority. A reused lowering
with missing providers must clear prior authority. A changed provider return
type must not match the consumer's previously resolved surface.

The flat bootstrap fixture inserts both actual HIR modules into the canonical
flat store. The nonflat fixture supplies providers through the entry lowering
API. Both require the same fixed signature; neither bypasses imports by appending
consumer text to a provider file.

The implementation joins caller-local symbols by defining module and physical
declaration name, checks structural scalar/pointer signature equality, and then
records authority under the caller symbol. Only demanded provider modules have
their function lists scanned. Duplicate provider owners cause a fatal diagnostic;
missing/mismatched/ordinary declarations retain unknown authority. No file or
environment reads are added. The driver captures its provider list once.

These are compiler representation assertions. Native linking, local raw C
output storage, LLVM execution and five-engine parity remain separate checks.
