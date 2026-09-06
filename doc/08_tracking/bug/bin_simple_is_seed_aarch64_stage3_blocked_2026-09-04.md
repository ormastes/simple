# `bin/simple` on this aarch64 host is the Rust seed, deliberately

**Status:** OPEN — stopgap in place, removal blocked on Stage 3
**Filed:** 2026-09-04
**Host:** aarch64-unknown-linux-gnu (Ubuntu 24.04, 20 cores, 121 GB)

## What was done and why

`bin/release/aarch64-unknown-linux-gnu/simple` is a copy of the **Rust bootstrap
seed**, not a self-hosted compiler. `.claude/rules/bootstrap.md` is explicit
that this must never be the resting state, and it is not being presented as one:
this record exists because that rule also requires filing one when the stopgap
is used.

It is used because Stage 3 self-host does not complete on this host. Stage 1
(seed) and Stage 2 (pure-Simple, admitted, independently verified non-vacuous —
152 MB, 515 dynamic symbols, reports `simple-bootstrap 1.0.0-rc.1` rather than
the seed banner) both succeed. Stage 3 fails in
`aot:lower_to_mir`, preceded by a malformed `HirType` reaching post-mono
verification. See
`doc/08_tracking/bug/zerokind_is_a_corrupt_aggregate_2026-09-03.md`, which this
session advanced (E-MIR-TYPE-ZeroKind raises 3 -> 0) but did not close.

Without Stage 4 there is no full-CLI pure-Simple binary, and without a
`bin/release/<triple>/simple` `scripts/setup/setup.shs` exits before generating
any MCP/T32 wrapper — so no MCP server could be registered at all.

## The seed says what it is

It has not been laundered into looking self-hosted. Running it prints, on every
invocation:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it
as the normal tool. Build and use the pure-Simple bin/simple instead.
```

and `--version` reports `Simple Language v1.0.0-rc.1` behind that banner.

## What this does NOT license

- It is not a substitute for a bootstrap. `simple test` passing under it does
  not demonstrate self-hosting.
- Do not refresh it to "keep it current". The failure mode `bootstrap.md`
  warns about is precisely a freshly-copied seed whose mtime makes the next
  lane's provenance check believe a real deploy happened.
- Do not commit it. `bin/release/**` binaries are not added here.

## Removal

Delete the seed copy and re-run
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy` once
Stage 3 self-host is green on aarch64. That is the only exit condition.
