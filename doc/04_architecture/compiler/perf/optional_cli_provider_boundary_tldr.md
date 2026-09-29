# Optional CLI provider boundary — TLDR

The CLI currently imports Office and UI implementations directly. Office
reaches all GPU backends; UI access reaches C SQLite. The full Stage4 CLI
compiles but fails on 173 optional symbols, and an isolated Office product
still fails on 106 GPU symbols.

Put only command metadata and receipt validation in the CLI kernel. Build
Office/UI as installed, cached provider artifacts; load in-process GPU/SFFI
facets on first use through versioned ABI admission. Extract the Office
software paint path from the all-backend engine without changing pixels.
Prefer PureDatabase for UI access only after parity proof. Bind retained
symbols and provider actions through `RuntimeFeatureClosureV1`.

The cutover needs atomic artifact packaging, command/error parity, missing
and incompatible provider tests, and matched hello/startup/RSS cohorts. See
`optional_cli_provider_boundary.md` for paths and sequence.
