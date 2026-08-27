# RISC-V HAL migration evidence

The RV32 boot-layout, RV64 boot-TCP, RV64 freestanding-policy, and RV64
no-allocation PMM gates are evidence producers, not bootstrap or QEMU launchers.
Every producer fails closed unless the operator supplies an admitted,
current-tree, pure-Simple Stage 4 full CLI and its exact provenance file:

```sh
sh scripts/check/check-rv32-boot-layout-branch-coverage.shs \
  --admit /absolute/path/to/stage4/simple \
  /absolute/path/to/stage4/simple.provenance.env
```

Use the same `--admit BINARY PROVENANCE` suffix for:

- `check-rv64-boot-tcp-policy-migration.shs`;
- `check-rv64-freestanding-policy-migration.shs`;
- `check-rv64-noalloc-pmm-migration.shs`.

The shared verifier rejects symlinked/non-canonical inputs, a Rust seed, an
invalid Stage 4 receipt, and a Stage 4 receipt that does not match the current
source tree. `SIMPLE_BIN` is intentionally not a fallback authority.

## Runtime and toolchain prerequisites

| Gate | Required execution runtime | Additional target prerequisite |
|---|---|---|
| RV32 boot layout | The admitted Stage 4 CLI's embedded runtime | None; this is compiler coverage, not RV32 hardware execution |
| RV64 boot-TCP | The admitted Stage 4 CLI's embedded runtime | Host C compiler for the independent oracle |
| RV64 freestanding policy | `SIMPLE_HOST_RUNTIME_PATH/libsimple_runtime.a` (default debug runtime archive) | `RISCV64_CC` (default `riscv64-unknown-elf-gcc`) plus `nm` and `readelf` |
| RV64 no-allocation PMM | `SIMPLE_HOST_RUNTIME_PATH/libsimple_runtime.a` (default debug runtime archive) | Host C compiler, `gcov`, `nm`, and `readelf` |

The producer records the canonical runtime path and SHA-256. Freestanding also
records the resolved RISC-V cross-compiler path and SHA-256. Missing runtime or
toolchain material is a hard failure before a PASS receipt can be published.

## Durable receipts

On PASS, each gate atomically publishes an env receipt under
`build/test-artifacts/riscv-hal-migration/<lane>/receipt.env`. Set
`HAL_MIGRATION_RECEIPT` to choose another durable path. Receipts include:

- Stage 4 binary and provenance paths and SHA-256 values;
- target runtime kind, path, and SHA-256;
- checker and scoped source/fixture hashes;
- exact scoped outcomes and artifact hashes;
- `qemu=not-run`; and
- a SHA-256 of the receipt payload before its final hash field.

The receipt proves only the named gate. It is not QEMU, board, whole-HAL, or
whole-file migration evidence.

## Freestanding decision-audit pin

`test/fixtures/os/rv64_freestanding_policy_decision_audit.sdn` pins the raw
SHA-256 of
`src/os/kernel/arch/riscv64/freestanding_policy.spl`. Recompute it directly and
update the single `meta owner_source_sha256` value whenever that owner changes:

```sh
sha256sum src/os/kernel/arch/riscv64/freestanding_policy.spl
```

The named-decision-row hash is different: it binds compiler-emitted line and
column rows and may only be refreshed by an admitted runtime gate. Do not infer
or fabricate that value from source text.

Run the bounded source contract without invoking compiler/runtime/QEMU gates:

```sh
sh scripts/check/test-riscv-hal-migration-evidence-contract.shs
```
