# Default Native Runtime Shift To C-Core ABI

## Decision

Native app builds now distinguish three host runtime lanes:

- `simple-core`: the preferred lane for non-compiler host binaries when a pure-Simple core runtime archive is present. It links `libsimple_runtime.a` only and satisfies the narrow C-compatible host ABI.
- `core-c-bootstrap`: the bootstrap/fallback lane for non-compiler host binaries when `simple-core` is not present yet. It also links `libsimple_runtime.a` only.
- `rust-hosted`: the hosted/legacy lane. It links `libsimple_native_all.a` and is selected automatically for compiler-like entries or explicitly through `--runtime-bundle rust-hosted` (legacy aliases: `hosted`, `all`).

## Rationale

- The existing non-compiler default should not silently escalate to the broad hosted runtime root.
- Host tools and small native apps need an auditable closure guard so size and dependency regressions fail loudly.
- Compiler/bootstrap entries still need the hosted lane until their remaining runtime dependencies are split further.

## Link-Selection Contract

1. `--runtime-bundle auto` resolves to `simple-core` for non-compiler host entries when that lane is available; otherwise it resolves to `core-c-bootstrap`.
2. `--runtime-bundle auto` resolves to `rust-hosted` for compiler-like entries under `src/compiler/**` and `src/app/cli/**`.
3. `--runtime-bundle simple-core` forces the pure-Simple core lane and fails clearly if the lane archive is not installed yet.
4. `--runtime-bundle core-c-bootstrap`, `core-c`, `core`, `core_c`, and `runtime` all force the bootstrap core lane.
5. `--runtime-bundle rust-hosted`, `hosted`, and `all` all force the hosted lane.
6. The `simple-core` and `core-c-bootstrap` lanes may not fall back to `libsimple_native_all.a`; doing so is a hard error.

## Diagnostics

- If a default-lane build would pull `libsimple_native_all.a`, the build fails with an explicit hosted-opt-in diagnostic.
- If a selected core lane link fails with unresolved hosted-only runtime symbols, the linker error includes a note directing the user to `--runtime-bundle rust-hosted`.
