# Class-field array elements inherit an incorrect nested-array shape

Status: repaired; focused Windows native verification passed. Formal bootstrap admission remains separate.

The admitted Windows Stage 2 compiler with SHA-256
`f859e6a2a22618ab9447ca5c4aed5b5ed75c8e09b961c03f648c9a88191d38e5`
compiled and ran Hello, then failed the strict cold HIR diagnostic regression.
Text source paths printed as numbers and a present text dictionary key was
not found. Compilation and execution both returned zero; the semantic oracle
correctly rejected the output.

Small native programs showed that local `[text]` indexing and indexing through
a function argument work. Reading `self.values[0]` from a `[text]` class field
does not, with either inferred or explicitly annotated text locals. The emitted
program performs an array copy on the returned text element.

`register_composite_field_metadata` in
`src/compiler/50.mir/_MirLowering/module_lowering.spl` initialized
`field_array_element_type_name` to `__runtime_array__` for every Array and Slice
field, including scalar and text elements. Its consumers interpret that marker
as describing the **element**, so `lower_index_expr` decodes a text element as
an array handle and `maybe_copy_array_value` copies it as an array.

The repair sets the marker only when the declared element is itself Array or
Slice. Named element identities remain unchanged. The existing declared-field
HIR type and runtime-array registration still describe the outer container;
primitive fields therefore retain their container operations without falsely
marking their elements as arrays.

The native fixture
`test/fixtures/compiler/native_class_field_array_elements_main.spl` checks
local/argument controls, inferred and annotated class-field text, a dictionary
key obtained from that field, scalar integer/bool/float elements, and nested
array value-copy independence. A produced pure compiler must compile and run
the fixture with exact output; interpreter success is insufficient.

Pre-repair evidence is retained at
`C:/dev/simple-phase4-evidence/stage2-20f-diagnostic/`.
The repair compiler was built separately at
`C:/dev/simple-field-index-evidence/`, with a fixed bootstrap producer/runtime,
one worker, a 6 GiB cap, private caches and a 1,800-second compile bound.
It is diagnostic evidence, not formal Phase 3/4 or release admission.

## Verification

The repaired pure compiler SHA-256 is
`c56235151c94b3c93935a21520b14284b059c4815d0b6a4f65e5bf71c5fda274`.
Its diagnostic build compiled 1,233 modules without failures. It then compiled
and executed real Hello with exact output, the array-field fixture with its
exact PASS line, and the source-extracted cold HIR diagnostic with all five
cases and exact expected output. All compilation and execution exit codes
were zero. The strict diagnostic previously failed under the admitted
pre-repair pure producer despite returning zero.

Receipts: `C:/dev/simple-field-index-evidence/hello/result.json`,
`field-elements/result.json`, and `strict-regression/result.json` under that
same evidence directory. These prove focused LLVM/MSVC semantics, not whole
suite, Cranelift, Phase 3/4, or release qualification. Array/Slice metadata and
Named element preservation received independent source review; the executable
fixture covers primitive and nested Array fields, not every Slice/Named case.