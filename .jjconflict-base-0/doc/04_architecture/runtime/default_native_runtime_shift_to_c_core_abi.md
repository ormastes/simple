# Default Native Runtime Shift To C-Core ABI

## Decision

Native app builds now distinguish two host runtime lanes:

- `simple-core`: the preferred pure-Simple lane when an ABI-complete pure-Simple core runtime archive is present. It links `libsimple_runtime.a` only and satisfies the narrow C-compatible host ABI.
- `core-c-bootstrap`: the C bootstrap lane when `simple-core` is not present or not ABI-complete yet. It also links `libsimple_runtime.a` only.

## Rationale

- Native builds must not silently escalate to the broad hosted runtime root.
- Host tools and small native apps need an auditable closure guard so size and dependency regressions fail loudly.
- Compiler/bootstrap entries must either build on the Simple/C lanes or fail closed; Rust-hosted/native_all fallback is not a supported runtime lane.

## Link-Selection Contract

1. `--runtime-bundle auto` resolves to `simple-core` when that lane is ABI-complete; otherwise it resolves to `core-c-bootstrap`.
2. `--runtime-bundle simple-core` forces the pure-Simple core lane and fails clearly if the lane archive is not installed yet or is ABI-incomplete.
3. `--runtime-bundle core-c-bootstrap`, `core-c`, `core`, `core_c`, and `runtime` all force the C bootstrap core lane.
4. `--runtime-bundle rust-hosted`, `hosted`, `hosted-runtime`, `rust-runtime`, and `all` are removed and fail closed.
5. The `simple-core` and `core-c-bootstrap` lanes may not fall back to `libsimple_native_all.a`; doing so is a hard error.

## Diagnostics

- If any native-build path would pull `libsimple_native_all.a`, the build fails with an explicit Simple/C-lane diagnostic.
- If a selected core lane link fails with unresolved hosted-only runtime symbols, port the missing ABI to `simple-core` or `core-c-bootstrap`; do not opt into a Rust-hosted lane.
