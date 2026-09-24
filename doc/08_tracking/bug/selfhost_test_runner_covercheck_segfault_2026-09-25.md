# Bug: self-hosted `simple test` segfaults right after cover-check

Date: 2026-09-25
Binary: `bin/release/aarch64-apple-darwin-macho/simple` (aarch64-apple-darwin)

## Symptom

Every `simple test <spec>` invocation — in both default JIT and
`--mode=interpreter` — dies with `Segmentation fault: 11` immediately after:

```
[setup] discover: 0ms (1 file(s))
[setup] cover-check: 0ms
```

No spec body output is produced. Reproduced on multiple
`test/01_unit/app/mcp/*_spec.spl` files and
`test/02_integration/app/mcp_stdio_integration_spec.spl`.

The same binary's `check` subcommand also misbehaves: it emits thousands of
spurious `HIR lowering error ... missing module surface` / `unresolved name`
diagnostics for code that compiles cleanly under the Rust seed, and exits 1.

## Workaround

Use the Rust seed (`bin/simple`) with `--mode=interpreter` for test/verify
runs until the self-hosted binary is redeployed from current pure-Simple
sources. This is the accepted seed fallback pattern used by the rendering
showcase gates (see `scripts/check/check-rendering-showcase-captures.shs`).

## Follow-up

Rebuild/redeploy the self-hosted binary via the bootstrap pipeline
(`scripts/bootstrap/bootstrap-from-scratch.sh`) from a healthy tree and confirm
`simple test test/01_unit/app/mcp/pipe_surfaces_spec.spl` no longer segfaults.
