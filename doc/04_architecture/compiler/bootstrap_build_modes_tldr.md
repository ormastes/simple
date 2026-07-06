# Bootstrap Build Modes TLDR

Purpose: keep bootstrap and native-build mode policy out of the Rust seed and
inside pure-Simple tooling.

- Default mode is `dynload`: reuse native cache when compiler/AOP/loader inputs
  are unchanged and emit native plus SMF cache artifacts where supported.
- `one-binary` is the conservative monolithic native executable path.
- Normal bootstrap never rebuilds Rust; `--full-bootstrap` is the only cargo
  rebuild path.
- `--entry-closure` is a reducer, not authoritative dependency tracing.
- AOP/MDSOC weaving, module resolver, interpreter cache, loader ABI, or compiler
  ABI changes invalidate broadly.
- Rust seed tools warn users to build/use pure-Simple `bin/simple`.

Next paths: `scripts/bootstrap/bootstrap-from-scratch.sh`,
`src/app/io/_CliCompile/compile_targets.spl`,
`src/compiler/80.driver/driver.spl`,
`src/compiler/99.loader/module_resolver/`,
`src/compiler/85.mdsoc/`.
