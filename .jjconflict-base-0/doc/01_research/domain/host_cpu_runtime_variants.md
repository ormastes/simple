# Host CPU Runtime Variants — Domain Research

- Host capability files should be machine-local, writable, and stable across runs; cache directories are the right default and explicit env overrides are useful for tests.
- Dynamic runtime loading should prefer the best compatible sibling binary and then fall back to a common scalar build.
- Variant manifests should keep the legacy single-variant contract while adding an index for multi-variant payloads so old packages remain readable.
- Admin-facing capability files should allow only downscoping. Invalid upscopes should be clamped and rewritten to the canonical supported subset.

