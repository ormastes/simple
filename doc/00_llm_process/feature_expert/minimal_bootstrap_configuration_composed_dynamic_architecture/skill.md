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

Research lives in
`doc/01_research/{local,domain}/minimal_bootstrap_configuration_composed_dynamic_architecture.md`.
The SPipe state is
`.spipe/minimal_bootstrap_configuration_composed_dynamic_architecture/state.md`.
