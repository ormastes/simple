# Diagnostic object matrix requests an object from package documentation

Status: diagnosed; narrow UNSUPPORTED classification repaired, aggregate admission remains blocked.

The module diagnostics inventory requests an object from `src/app/__init__.spl`.
That file contains only full-line comments and blank lines, including commented
usage examples. It has no imports, exports, functions, types or executable
initializers. No code/import closure is present to lose.

Producer `4c479a0d3f25bcb73a9c4c8fe1735b7743c65862076c73e079b7f7bc9c607036`
failed this request with status 1. The retained row is
`/mnt/wsl/simple-dbc-native-bootstrap-20261012/stage2-compiler-tests/x86_64-unknown-linux-gnu/verification/module-diagnostics/attempt.DRRknu/1/row`.
Its compile log reports `native-build produced no code-bearing MIR modules`
after zero frontend diagnostics and completed native-cache scanning. The prior
041e685f producer reported the same package-init failure.

This diagnostic uses `--emit-object` and independently requires a nonempty
ELF/COFF/Mach-O relocatable object. A documentation-only source cannot meet that
artifact contract. Producing a stub object or labeling it PASS would be false
evidence. General app/compiler/lib checks and actual tool entrypoint builds
remain required and are not waived by this diagnosis.

`bootstrap_module_documentation_only` conservatively recognizes only regular,
readable, nonsymlinked files containing blank lines/full-line comments. Imports,
exports, docstrings, attributes, declarations and unknown syntax remain on the
real compiler path. The matrix now records explicitly UNSUPPORTED for this
object operation, with no claimed artifact, source SHA and selected producer
SHA. Authority and source stability are rechecked before recording it. The
aggregate remains failed. A policy repair still needs actual empty-input
rejection and code-bearing facade/object evidence; this row is not an executed
PASS and does not silently remove the input from required coverage.

The focused shell fixture exercises documentation plus code-bearing/import/
export/docstring/attribute/symlink/missing inputs. No compiler build or live
frozen-source modification was performed by this diagnosis lane.
