<!-- codex-design -->
# Native-build environment timeout architecture

`ConfigEnv` is the Rust configuration capsule: it derives a scoped key and resolves a typed value once at each CLI boundary. `NativeBuildConfig` remains a pure downstream configuration object and does not read environment state. Rust driver and `native_all` call the same resolver, then pass the resolved per-file value into `NativeBuildConfig.file_timeout`.

The Pure-Simple launcher owns only the outer-worker key. Its worker timeout never inherits the per-file key, preventing a per-file tuning value from bounding the aggregate process.

`ArgParser` mirrors the name-derivation and explicit-key behavior for Pure-Simple applications. It does not import arbitrary environment keys.
