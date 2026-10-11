# Native fixture qualification: array field elements

Status: scoped integrated-candidate fixtures PASS; draft release head and broader admission PENDING.

## Producer and source identity

- Integrated compiler source: `57d83549f09b374ff9105018896843d4f8ff00e9`.
- Pure-Simple producer: `/home/yoon/dev/simple-bootstrap-next-20261011/build/native_probe/final-integrated/simple`.
- Producer SHA256: `e9e8762c79e47d1c0db418d2a8ff5d5eda7b1ef8744ccff32227ae7463926491`.
- LLVM18 llc: `/usr/lib/llvm-18/bin/llc`, SHA256 `682c25e9be136578115664d3f62e067ddd8f2f3f92830c6d42d8c9cee2d74884`.
- Runtime bundle: `core-c-bootstrap`; runtime path `/home/yoon/dev/simple-release-1.0-codex/src/compiler_rust/target/bootstrap`.
- Release rebase target: `d71b8bcf76d4cad6259002930078958a2cb2d827` (`release/1.0`).
- This producer includes other coordinated fixes. The independently rebased PR head has not been rebuilt.

## Fixture receipts

- `test/fixtures/compiler/u16_array_comparison.spl`: SHA256 `9d93badf7af9b068a1a9fc21cca4e86c60cb38abdf5cd0bf435f6517506b204d`.

| Artifact | ELF e_machine | SHA256 |
|---|---:|---|
| u16-arm | 183 | `98b36574f6e1a4b399156144ad99484db330a318719c8b83a5a52bd2ed519acd` |
| u16-riscv.o | 243 | `176788af8c8ce3950c9c3fffeb59afb456db0fa8ca5c0c64ac034a5d643f8d97` |

## Results

- ARM build exit 0; executable exit 0, stdout `U16_ARRAY_COMPARISON_PASS`. Plain/field/nested u16 reads, zero/high values and mask controls passed.
- RISC-V object build exit 0; actual ELF machine 243. No RISC-V execution attempted.

## Commands and retained evidence

All builds were sequential, pinned to CPU 19 with one native worker and a 120-second timeout. ARM execution used a 15-second timeout. Environment:

```text
SIMPLE_SCV_INVENTORY_COLD_INIT=1
SIMPLE_BOOTSTRAP=1
SIMPLE_NO_STUB_FALLBACK=1
SIMPLE_KERNEL_K1_POLICY=llvm-cranelift
SIMPLE_PLUGIN_MANIFEST_POLICY=simple-sdn
SIMPLE_RUNTIME_PATH=/home/yoon/dev/simple-release-1.0-codex/src/compiler_rust/target/bootstrap
SIMPLE_LLVM_BIN=/usr/lib/llvm-18/bin
```

```sh
taskset -c 19 timeout 120 /home/yoon/dev/simple-bootstrap-next-20261011/build/native_probe/final-integrated/simple native-build --source test/fixtures/compiler --entry-closure --entry test/fixtures/compiler/u16_array_comparison.spl --backend llvm --threads 1 --cache-dir build/native_probe/final-cast-qualification/u16-arm-cache -o build/native_probe/final-cast-qualification/u16-arm --runtime-bundle core-c-bootstrap --runtime-path /home/yoon/dev/simple-release-1.0-codex/src/compiler_rust/target/bootstrap
```

```sh
taskset -c 19 timeout 120 /home/yoon/dev/simple-bootstrap-next-20261011/build/native_probe/final-integrated/simple native-build --source test/fixtures/compiler --entry-closure --entry test/fixtures/compiler/u16_array_comparison.spl --backend llvm --threads 1 --cache-dir build/native_probe/final-cast-qualification/u16-riscv-cache -o build/native_probe/final-cast-qualification/u16-riscv.o --target riscv64-unknown-linux-gnu --emit-object
```

Raw commands, JSON receipts, complete build/runtime logs and artifact hashes are retained at:
`/home/yoon/dev/simple-llvm-cast-roots-20261011/build/native_probe/final-cast-qualification`.

## Pending release gates

- Authored SSpec/unit execution with a qualified pure-Simple test runner.
- Native construction and fixture qualification of this isolated release PR head.
- Full compiler/lib/MCP/LSP checks, core and MCP smoke, and whole-suite tests.
- Canonical producer admission and release verification; no merge or admission is claimed.
- Original exhaustive failing-module matrix rerun is not part of these scoped fixtures.
