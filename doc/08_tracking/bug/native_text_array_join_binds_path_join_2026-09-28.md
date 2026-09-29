# Native text-array join binds path join in archive closure

Status: open compiler bug; cache/archive caller workaround in
`codex/target6-cas-publication-guard-20260928`.

A no-stub Stage2 native archive publish/load probe compiled 69 source units
without failure, then segfaulted in `lib.nogc_sync_mut.path.path_join`.
The GDB stack placed its caller at
`package_archive_manifest_v1`, whose source called
`dependencies!.join(",")` on `[text]`. The path function has a different
contract and must not satisfy a text-array method call. The compiler also
warned about other same-named methods with erased receiver types.

The affected CAS/archive caller now invokes an explicit text-builder helper
with a checked return value. The rebuilt 70-unit native probe publishes,
loads, pins, and decodes archive receipts for zero and one dependency.

The compiler still needs a method-binding repair: preserve the receiver type
through native codegen, reject ambiguous erased calls, and prove that
`[text].join` cannot dispatch to a path function in a mixed import closure.
