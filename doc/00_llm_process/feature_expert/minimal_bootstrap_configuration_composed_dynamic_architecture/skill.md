# Feature Expert: Minimal-Bootstrap Configuration Composition

## Canonical guidance

Use [Minimal-Bootstrap Feature Development](../../../07_guide/compiler/minimal_bootstrap_configuration_composition.md)
for build selection, provider/SCI boundaries, receipts, and bootstrap reasons.

## Expert routing

- Composition source compiles into one immutable `SimpleCompositionImageV1`;
  runtime does not merge text or compile missing providers.
- Providers expose versioned interface groups through
  `SimpleProviderQueryV1`; compiler internals remain opaque.
- Begin every feature lane with the smallest named target, provider, and SCI
  projection. A compiler path is not a bootstrap reason.
- `Unknown` compatibility rebuilds the smallest relevant closure and never
  authorizes reuse.
- Preserve self-host convergence and DDC as explicit release/trust targets.

## ABI-digest admission checklist

- Treat the v1 provider result as exactly 84 bytes: the established 48-byte
  scalar prefix, the full ABI SHA-256 at bytes 48..79 in display order, and
  four zero reserved bytes at 80..83.
- Poison-fill host-owned result storage before a foreign provider call so a
  legacy 60-byte partial write fails closed instead of inheriting zeroes.
- Compare the complete canonical SCI ABI digest before publishing a session
  pin; distinguish malformed SCI input from an exact digest mismatch.
- Keep `test/03_system/app/simple/feature/sci_provider_query_abi_digest_spec.spl`
  and its Markdown-only `doc/06_spec` manual aligned. Execute it only through
  an admitted general pure-Simple CLI; otherwise record `TEST_BLOCKED`.
- Do not treat this identity gate as loader TOCTOU proof. Mutable paths and
  same-handle replacement remain a separate later criterion.

Research lives in
`doc/01_research/{local,domain}/minimal_bootstrap_configuration_composed_dynamic_architecture.md`.
The SPipe state is
`.spipe/minimal_bootstrap_configuration_composed_dynamic_architecture/state.md`.
