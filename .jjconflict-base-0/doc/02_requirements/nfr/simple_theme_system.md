# NFR Targets: Simple Theme System

## NFR-001: Round-trip Latency
- **Target**: Generating a Stitch payload from a `.simple-theme` file should take < 100ms.

## NFR-002: Parsing Robustness
- **Target**: The CSS parser should handle common CSS syntax variations (comments, whitespace, units) without failing.
- **Mechanism**: Use a regex-based or lexer-based variable extractor.

## NFR-003: Platform Consistency
- **Target**: Visual parity (colors and layout) should be maintained between baremetal and web renderers using the same `.simple-theme` file.

## NFR-004: Low Overhead
- **Target**: No runtime parsing of CSS on baremetal hot-paths. CSS should be parsed once at theme load and converted to numeric constants.
