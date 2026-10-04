# Duplicate nominal layout characterization

Base: b1668eac56919dc6c48a3dfece87333c51683eb5. The live Phase2
warnings select field slot0/ANY for unresolved `ElfSymbol.name` and
`SymbolId.name`. This fixture preserves the duplicate names and incompatible
layouts; it does not rename production types or bypass field checking.

`test/04_smoke/nominal_layout/a.spl` places ElfSymbol.name at slot0 and
defines SymbolId(id:i64). `b.spl` places ElfSymbol.name at slot6, with a
distinct integer st_name at slot0, and defines SymbolId(name:text).
The entry checks25 actual values: every ELF field, module-owned parameter
accessors, record returns, array elements, both SymbolId values, and nested
SymbolId fields. Ordinary failed comparisons accumulate rather than stopping
the remaining checks. A process crash is not a passing or complete run.

Compile the entry with `--source test/04_smoke/nominal_layout --entry
test/04_smoke/nominal_layout/main.spl --entry-closure --threads 80`, using the
normal core-C runtime/toolchain/source inventory setup. Run the produced
binary. Success requires exit0,25 distinct PASS lines, no FAIL lines, and the
final `Nominal layout: 25 checks, 0 failures` line. Retain stdout, stderr,
compiler SHA, source SHA, backend and exact command. A module-resolution or
compilation failure means runtime checks are UNRUN, not25 failed assertions.

Run separate seed-bootstrap diagnostic and refreshed pure-Phase2 compiler
lanes for both LLVM and Cranelift. Use private validated entry caches; do not
change a live source snapshot to install this fixture. The short directory
and module names avoid the known Windows long object-basename defect.

Runtime status: **UNRUN**. This source-only regression is not evidence that
duplicate owner resolution has been repaired. The negative case (accessing
name on the numeric-only SymbolId) also needs rejection coverage when the
compiler owner repair is implemented.
