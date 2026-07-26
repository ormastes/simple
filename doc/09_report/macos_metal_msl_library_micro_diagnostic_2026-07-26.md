# macOS Metal MSL library micro-diagnostic — blocked evidence (2026-07-26)

## Status

- status: blocked-before-native-run
- native diagnostic: not run
- full-live/window harness: not run

## Exact blocking prerequisite

The default trusted manifest is absent in this worktree:

```text
build/macos_gpu_2d_live_native/metal/trusted-build.env
```

The checker therefore cannot establish its required binding among the canonical
self-hosted compiler, Metal runtime provider, C runtime provider, and their
SHA-256 values. The arm64 release compiler candidate exists, but that alone is
not sufficient and was not used to start a native build.

## What this does and does not prove

The committed source and contract specs cover the exact Engine2D MSL source,
typed error ABI, cleanup/reporting contract, process supervision, and
manifest-admission rules. They are not evidence that macOS created the library,
loaded the provider, or rendered a frame. Native evidence remains blocked until
a current passing trusted manifest and its exact bound providers are present.

## Static manifest-admission repair

The micro-checker now selects the exact compiler and providers recorded by the
canonical manifest. It accepts only the producer-issued frozen Stage-3 or
legacy repository-release identity/source-kind pairs, requires current
repository and complete source-input provenance, exact hashes, non-symlink
executables, and rejects seed/debug artifacts. No native diagnostic or
full-live/window command was run for this repair; the blocked status remains.
