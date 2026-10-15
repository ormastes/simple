# Imported positional struct pattern field order

C34's real MIR serializer closure failed on positional patterns naming imported
`MirLocal`, `MirBlock`, `SwitchCase` and `SymbolId`: each was diagnosed as an
unknown enum variant. The `Some(SymbolId(raw))` case subsequently reported an
undefined `raw`; the `MirBlock(..., instructions, ...)` case reported an I64
collection in its `for` loop. These downstream errors are candidate consequences
of the failed pattern binding, not separately proven runtime fixes.

Frozen evidence is under
`/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c34-producer-mir-json-fragments-attempt1/`:
`normalized-mir-errors.json`, `mir-error-groups.json`, and `construction.log`.
Producer SHA-256: `f00dbc9c608dfaf22a15736747799821ed1b75871bf45ad3fe1b133701030e81`;
producer source: `20a93224b3f08a86a15b520252bd95965f1e6423`;
serializer candidate source: `1a5a70e37296b247ac3052aaa26a7a0b62e75c31`.
The failed run observed 98 HIR modules; it produced no successful MIR receipt
or native object. Source base for this repair is release
`6b8a3e8b51071c92d1ddf0faf9ec4004e8ecd2ab`.

## Cause and correction

The frontend represents `Record(a, b)` patterns as unqualified enum patterns.
HIR already reclassifies them as struct patterns when declaration field order
is available. Local declaration prescan registers both field types and order.
Imported composite registration previously registered only field types, so the
pattern classifier could not recognize imported structs and left them on the
enum path.

Import registration now records field order in the existing map under the
canonical defining-module/name key, in the declaration's original order.
Pattern classification first resolves the lexical spelling to its symbol,
requires a struct/class declaration and looks up that exact canonical key.
Local legacy fallback is limited to the current module or an originless local;
foreign declarations never borrow a bare-name layout. Existing enum-variant
collision handling remains in force. No new HIR fields, codec revisions,
runtime ABI changes, module imports or privacy relaxation are introduced.

## Regression and qualification

`test/fixtures/compiler/imported_positional_struct_owner/` exercises two imported
aliases with the same basename but different field orders, a same-named local
struct, array payload iteration, and `Some(SymbolId(raw))`/nil matching.
Its ARM oracle is exit zero with exactly
`imported_positional_struct_owner: PASS` on stdout. After that passes, require
an explicitly targeted LLVM 18 RISC-V object with ELF machine 243. An object
check is not RISC-V execution.

`test/01_unit/compiler/hir/imported_positional_struct_owner_spec.spl` includes
actual parsed multi-module HIR/MIR lowering and negative owner/kind metadata
cases. All executable qualification is pending a coordinated changed-source
producer. No compiler build or rerun of the failed C34 serializer was performed
for this repair. The unrelated named-enum constructors, Optional payload type
compatibility, nil comparisons and other enum subject failures remain separate.
This source analysis does not claim the entire serializer closure is fixed.
