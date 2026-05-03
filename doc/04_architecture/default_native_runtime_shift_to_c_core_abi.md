# Default Native Runtime Shift To C-Core ABI

## Decision

Native app builds now distinguish two host runtime lanes:

- `core-c`: the default lane for non-compiler host binaries. It links `libsimple_runtime.a` only and represents the narrow C-compatible runtime ABI surface.
- `rust-hosted`: the hosted/legacy lane. It links `libsimple_native_all.a` and is selected automatically for compiler-like entries or explicitly through `--runtime-bundle hosted` (legacy alias: `all`).

## Rationale

- The existing non-compiler default should not silently escalate to the broad hosted runtime root.
- Host tools and small native apps need an auditable closure guard so size and dependency regressions fail loudly.
- Compiler/bootstrap entries still need the hosted lane until their remaining runtime dependencies are split further.

## Link-Selection Contract

1. `--runtime-bundle auto` resolves to `core-c` for non-compiler host entries.
2. `--runtime-bundle auto` resolves to `rust-hosted` for compiler-like entries under `src/compiler/**` and `src/app/cli/**`.
3. `--runtime-bundle core-c`, `core`, `core_c`, and `runtime` all force the `core-c` lane.
4. `--runtime-bundle hosted`, `rust-hosted`, and `all` all force the hosted lane.
5. The `core-c` lane may not fall back to `libsimple_native_all.a`; doing so is a hard error.

## Diagnostics

- If a default-lane build would pull `libsimple_native_all.a`, the build fails with an explicit hosted-opt-in diagnostic.
- If a `core-c` link fails with unresolved hosted-only runtime symbols, the linker error includes a note directing the user to `--runtime-bundle hosted`.
