# Optional Range generated codec

Executable source: `test/01_unit/compiler/hir/range_optional_codec_spec.spl`.

Four cases construct real HIR Range nodes, encode them with the generated codec, decode them, and assert byte-identical re-encoding and retained structural hashes. They cover both absent, absent start, absent end, and both present endpoints.

The fifth case encodes a real module, proves that its current regular encoding decodes, then replaces only the header with the prior regular version and requires rejection. It also asserts the new regular and canonical codec identities. Optional node encoding introduces another presence bit for present endpoints; version changes prevent stale cache decoding.

Evidence: the four unchanged topology cases passed in the initial Phase 1 run. The strengthened valid-module header case passed in a separate selected one-case run. The final five-case file was not rerun. No self-hosted native admission is claimed.
