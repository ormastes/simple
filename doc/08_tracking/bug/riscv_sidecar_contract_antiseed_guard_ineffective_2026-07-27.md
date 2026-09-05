# RISC-V sidecar-contract anti-seed guard is ineffective against a seed-clobbered `bin/release`

**Status:** open
**Found:** 2026-07-27 (Simple RISC-V hardening campaign, Lane C)
**Area:** `scripts/check/check-riscv-fpga-sidecar-contract.shs`
**Severity:** high — an evidence-integrity defect: the gate that exists to reject
seed-produced evidence silently accepts it

## Finding

`check-riscv-fpga-sidecar-contract.shs:9-14` decides whether it is being driven by
the Rust bootstrap seed with `is_rust_seed_simple()`, which tests **only whether
the binary path contains `src/compiler_rust/`**.

That check is path-based, so it catches the obvious case
(`src/compiler_rust/target/bootstrap/simple`) and misses the case that actually
happens in practice: **`bin/release/<triple>/simple` itself being a seed build**.
A seed-clobbered `bin/release/x86_64-unknown-linux-gnu/simple` has no
`src/compiler_rust/` in its path, so it passes the "must not be the Rust seed"
guard silently.

Confirmed on this host:

```
$ bin/simple --version
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
$ readlink -f bin/simple
/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
```

The binary announces itself as a seed on **stdout**, and the gate never looks.

## Why this matters

This is how an entire campaign's RISC-V evidence became seed-attributed without
anyone noticing. The `bin/release/simple` wrapper *does* refuse seeds correctly —
but the gate resolves and invokes `bin/release/<triple>/simple` directly, bypassing
the wrapper that would have caught it.

A gate whose stated purpose is to reject seed evidence, and which cannot detect the
most common seed situation, provides false assurance. Every green result it has
produced against a clobbered `bin/release` is unverified with respect to its own
core precondition.

## Reproduction

```bash
readlink -f bin/simple                     # -> bin/release/<triple>/simple
bin/simple --version | head -1             # -> "WARNING: ... bootstrap seed only"
sh scripts/check/check-riscv-fpga-sidecar-contract.shs   # guard does not fire
```

## Suggested fix

Probe the binary's identity instead of its path — the same approach
`bin/release/simple` already uses: run `"$SIMPLE_BIN" --version` and fail closed
when the seed warning banner is present. Path heuristics cannot survive a
clobbered deploy target; the banner is authoritative because the binary emits it
about itself.

Apply the same hardening to any sibling gate that uses a path-based seed test.

## Not changed here

Lane C deliberately did **not** patch this. Repairing the guard while the campaign
is mid-flight would change gate semantics under the other lanes and would mix an
evidence-integrity fix into an unrelated lane. Filed for a focused change.

## Related

- `doc/08_tracking/bug/riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27.md`
  — the seed-clobbered deploy target this guard fails to catch
- `doc/08_tracking/bug/seed_parser_rejects_multiline_if_expression_chain_2026-07-27.md`
- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md`
