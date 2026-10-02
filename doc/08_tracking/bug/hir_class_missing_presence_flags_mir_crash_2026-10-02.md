# Missing HIR class presence flags crash native MIR lowering

## Reproduction and evidence

A Linux Phase 2 compiler with SHA-256
`04d72b6adc0e9d1b6696f721bb4a088b5194f10d80642f0e43c2cdabb6c5444d`
successfully compiled an LLVM hello, but compiling the loader's
`src/compiler/99.loader/compiler_ffi.spl` closure exited 139 during MIR lowering.
The exact frozen source was `6b9edd328cc2fd3d7372c2c685a1b2256999fa1c`.

The retained GDB backtrace places the fault in `MirLowering.lower_class_type`,
at address `0x997c24` (`+1344`). The generated code tests the class's
`has_export_attr` byte at offset `0x60`, enters the true branch, loads the
`export_attr` value at offset `0x68`, clears its tag bits, and dereferences null.
This is a HIR presence/payload inconsistency, not an unresolved runtime provider.

The small native fixture
`test/01_unit/compiler/codegen/class_optional_metadata_native.spl` independently
reproduced exit 139 at MIR entry after 77 ms using the same compiler. It contains
one ordinary class with one field and no imports or export annotation. After
that reproduction, the fixture was extended with a documented, explicitly
exported class to cover positive metadata presence in after-fix validation.
The fixture was copied under the frozen checkout's ignored `build/native_probe`
directory; no frozen source files were changed. The guard reported quiescence.

Evidence is retained in D-backed Debian and in
`D:/dev/linux-mir-crash-20261002`: `gdb.log`,
`lower-class-disassembly.txt`, and `class-before-in-tree/`.
An earlier external `/mnt/d/...` fixture entry was rejected with zero collected
sources before code generation; its distinct evidence is retained in
`class-before/`. That entry-path limitation is not counted as a compiler-crash
reproduction or as fixed by this change.

## Fix

`HirLowering.lower_class` omitted three desugared presence fields while supplying
their payloads: `has_doc_comment`, `has_export_attr`, and
`has_specialization_of`. Function lowering already explicitly supplies these
flags and documents the seed's unsafe handling of omitted flags in partial
named construction.

Class lowering now copies the parser's doc-comment presence, computes export
presence using native-safe `if val`, and explicitly sets specialization presence
to false. Each flag is supplied in declaration order beside its payload. The
MIR consumer continues to trust the HIR contract; no nil-dereference guard masks
an inconsistent producer.

The underlying seed partial-constructor defaulting behavior remains a separate
language bug: an omitted boolean must not acquire a truthy nil sentinel. This
patch restores the compiler's explicit HIR construction contract without
claiming that generic constructor-default behavior is repaired.

## Validation status

Before-fix native reproduction is confirmed. After-fix native compiler rebuild,
class fixture execution, loader closure, and downstream Phase 3/4 remain pending.
No full production verification PASS is claimed.
