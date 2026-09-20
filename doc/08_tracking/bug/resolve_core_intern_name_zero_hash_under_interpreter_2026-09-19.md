# `resolve_core.intern_name` returned Hash128(0,0) for every name under the interpreter

- Date: 2026-09-19
- Status: **product mitigated** (resolve_core.spl); **seed interpreter defect OPEN**
  (same defect as `crypto_types_text_to_bytes_collides_with_base_encoding_2026-08-21.md`)
- Severity: high: every SMF/style link key collided silently, with no error

## Symptom

Under `bin/simple test` (interpreter), 4 specs were red:
`smf_link_profile_spec` 3/5, `smf_link_receipts_spec` 14/15,
`smf_reader_adapter_spec` (resolution example), and
`test/01_unit/common/structural/resolve_core_spec.spl` 6/7
("hashes two different texts to different Hash128 values").
A probe showed `intern_name("main") == intern_name("foo") == Hash128(0, 0)`,
so every symbol landed in one resolve group: references resolved to the wrong
definition with reason DuplicateDefinition.

## Root cause

`src/lib/common/structural/resolve/resolve_core.spl` imported
`crypto_text_to_bytes as text_to_bytes`. The alias puts the bare name
`text_to_bytes` back in play. The interpreter resolves free functions by bare
name, so in a non-entry module the call went to the `[u8]`-typed
`text_to_bytes` (string_core/base_encoding). `sha256_bytes` then did its
`<< 24` word assembly on u8-typed values, which truncated (h0 came out as 228,
not 225329273), and the digest bytes came back all zero.
Discriminator: the same code reached through the JIT, or called from the entry
module, hashed correctly.

## Mitigation (2026-09-19, linker lane A6)

`resolve_core.spl` now imports and calls `crypto_text_to_bytes` directly, with
no alias. Semantics are unchanged: the result is the SHA-256 that the JIT path
already computed. After the change all 5 specs above pass.

`style_link_profile.spl`/`style_link_receipts.spl` also use `intern_name`, so
they were hit by the same defect and are fixed by the same change.

## Open

The interpreter still ignores import aliases when it resolves bare names. Any
`use X.{a_unique as common_name}` whose `common_name` is also defined elsewhere
can hit the wrong function. Fixing the resolver is the remaining work.
