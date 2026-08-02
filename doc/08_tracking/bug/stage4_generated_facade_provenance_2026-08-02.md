# Stage4 generated facade provenance ambiguity

## Reproduction

The x86 Stage4 native build stopped while resolving `std.nogc_sync_mut.io`:

`ambiguous facade export: module=std.nogc_sync_mut.io item=file_append package=lib.nogc_sync_mut.io`

Both `io/file_ops.spl` and the compatibility `io/mod_stub.spl` declare the
name, while generated `io/__init__.spl` records the authoritative owner in the
immediately preceding `# Re-exported from file_ops.spl` comment.

## Fix

Module surfaces now preserve generated re-export owner comments as structured
export origins before sibling inference. Explanatory text after the `.spl`
filename is accepted. Explicit imports and direct declarations retain their
higher precedence, and an unhinted duplicate still fails closed.

## Regression evidence

`resolve_import_symbols_spec.spl` covers the exact concrete-vs-stub duplicate,
the explanatory-comment variant, and the existing unhinted ambiguity case.
Focused result: 16 examples, 0 failures.

## Native bootstrap compatibility

The Stage2 native compiler produced byte-identical resolver objects after a
loop-carried owner retention change, although the interpreter regression was
green. Generated facades therefore also repeat the authoritative provenance
comment before continuation export lines that contain ambiguous compatibility
names. This makes every such export independently attributable on old native
bootstrap compilers and remains compatible with the grouped parser.

The root `io.spl` facade is a separate module from `io/__init__.spl`. Its broad
self-glob now has explicit imports for the concrete `file_ops`, `dir_ops`, and
`file_shell` owners, so compatibility stubs cannot win or make those exports
ambiguous during Stage4 extraction.
