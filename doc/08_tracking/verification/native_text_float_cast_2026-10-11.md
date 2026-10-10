# Native fixture qualification: text float cast

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

- `test/fixtures/compiler/float_pointer_cast_invalid.spl`: SHA256 `63358fecab89230866a1ccb6af6e6bc798c54a49641d708d1b18822919d8749d`.
- `test/fixtures/compiler/float_text_cast_invalid.spl`: SHA256 `bdf8c79b048cd7674fa8b237efcc667b8fdc1a71f766ef68b582329d4d859b31`.
- `test/fixtures/compiler/float_text_cast.spl`: SHA256 `5c8c040c1d1d7dd55e0c6fc0ae23ab85474bc72f4f5c6c6d23894959cd2aeaae`.

| Artifact | ELF e_machine | SHA256 |
|---|---:|---|
| float-arm | 183 | `f0a4c8545614ae3bff1adf0db0aac19cedf0563e9412f448dbc477e471744441` |
| float-invalid-arm | 183 | `d3817efd11e8fb70aad05aefda1618ddf3082fc1d2c8fd8a7d48341f331021b7` |
| float-riscv.o | 243 | `af3a423fba31c81002bbb08483a6e7e171b2be7e8c1779ea2a555c2d9c35ae52` |

## Results

- ARM positive build exit 0; executable exit 0, stdout `FLOAT_TEXT_CAST_PASS`. Decimal, exponent, zero, explicit f64 and numeric conversion controls passed.
- ARM malformed text build exit 0; executable exit 1, stdout/stderr `panic: cannot parse text as floating-point value`; no unreachable acceptance marker.
- ARM class-to-float build exit 1 with fatal MIR diagnostic `floating-point conversion requires a numeric value or text; pointer/aggregate conversion is unsupported` at fixture line 6. No artifact emitted.
- RISC-V positive object build exit 0; actual ELF machine 243. No RISC-V execution attempted.

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
taskset -c 19 timeout 120 /home/yoon/dev/simple-bootstrap-next-20261011/build/native_probe/final-integrated/simple native-build --source test/fixtures/compiler --entry-closure --entry test/fixtures/compiler/float_text_cast_invalid.spl --backend llvm --threads 1 --cache-dir build/native_probe/final-cast-qualification/float-invalid-arm-cache -o build/native_probe/final-cast-qualification/float-invalid-arm --runtime-bundle core-c-bootstrap --runtime-path /home/yoon/dev/simple-release-1.0-codex/src/compiler_rust/target/bootstrap
```

```sh
taskset -c 19 timeout 120 /home/yoon/dev/simple-bootstrap-next-20261011/build/native_probe/final-integrated/simple native-build --source test/fixtures/compiler --entry-closure --entry test/fixtures/compiler/float_pointer_cast_invalid.spl --backend llvm --threads 1 --cache-dir build/native_probe/final-cast-qualification/pointer-invalid-arm-cache -o build/native_probe/final-cast-qualification/pointer-invalid-arm --runtime-bundle core-c-bootstrap --runtime-path /home/yoon/dev/simple-release-1.0-codex/src/compiler_rust/target/bootstrap
```

```sh
taskset -c 19 timeout 120 /home/yoon/dev/simple-bootstrap-next-20261011/build/native_probe/final-integrated/simple native-build --source test/fixtures/compiler --entry-closure --entry test/fixtures/compiler/float_text_cast.spl --backend llvm --threads 1 --cache-dir build/native_probe/final-cast-qualification/float-riscv-cache -o build/native_probe/final-cast-qualification/float-riscv.o --target riscv64-unknown-linux-gnu --emit-object
```

The positive ARM command uses the same options as `float-invalid-arm`, with entry `float_text_cast.spl` and output/cache stem `float-arm`.

Two initial admission attempts performed no compilation: the `build/` source root was unsupported, then the supported fixture root required explicit cold inventory initialization. The documented checks use the corrected source-authority route.

Raw commands, JSON receipts, complete build/runtime logs and artifact hashes are retained at:
`/home/yoon/dev/simple-llvm-cast-roots-20261011/build/native_probe/final-cast-qualification`.

## Pending release gates

- Authored SSpec/unit execution with a qualified pure-Simple test runner.
- Native construction and fixture qualification of this isolated release PR head.
- Full compiler/lib/MCP/LSP checks, core and MCP smoke, and whole-suite tests.
- Canonical producer admission and release verification; no merge or admission is claimed.
- Original exhaustive failing-module matrix rerun is not part of these scoped fixtures.
