# Compiler host nullable file reads

The executable scenario is
`test/01_unit/compiler/driver/compiler_host_nullable_file_read_spec.spl`.
Runtime qualification remains pending an admitted self-hosted compiler.

The test checks the contract used by compiler source, manifest, cache, and
watcher readers: a missing file yields `nil`, an existing empty file yields
empty text, and a populated file yields its exact text. The migrated callers
preserve their existing `??` fallbacks and optional-value checks.
