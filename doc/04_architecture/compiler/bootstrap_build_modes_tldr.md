# Bootstrap Build Modes TLDR

Purpose: keep bootstrap and native-build mode policy out of the Rust seed and
inside pure-Simple tooling.

- Default mode is `dynload`: preserve compiler-owned per-module cache entries,
  rebuild Stage 2/3 pure-Simple artifacts, and skip the Stage 4 full CLI relink.
- Use `--full-cli` or `--deploy` for Stage 4. `--full-bootstrap` controls Rust
  seed/runtime freshness and does not imply a monolithic CLI build.
- `one-binary` is the conservative monolithic native executable path.
- Normal bootstrap never rebuilds Rust; `--full-bootstrap` is the only cargo
  rebuild path.
- Stage 3 invokes positional `bootstrap_main.spl` through pure Simple with the
  native-all bundle; it forwards and restores runtime path, target, cache, and
  thread settings. Explicit `--entry` remains the Stage 2 Rust bridge.
- The focused Stage 4 route forwards canonical `--low-memory` through
  `SIMPLE_BOOTSTRAP_LOW_MEMORY` and restores the prior environment value.
- Use full bootstrap only when changed Rust seed/runtime implementation inputs
  must actually be rebuilt; final gates and pure-Simple changes use the cheapest
  adequate incremental or staged pure-Simple build.
- `--entry-closure` is a reducer, not authoritative dependency tracing.
- AOP/MDSOC weaving, module resolver, interpreter cache, loader ABI, or compiler
  ABI changes invalidate broadly.
- Rust seed tools warn users to build/use pure-Simple `bin/simple`.

Next paths: `scripts/bootstrap/bootstrap-from-scratch.sh`,
`src/app/io/_CliCompile/compile_targets.spl`,
`src/compiler/80.driver/driver.spl`,
`src/compiler/99.loader/module_resolver/`,
`src/compiler/85.mdsoc/`.
