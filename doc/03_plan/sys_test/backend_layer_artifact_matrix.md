<!-- codex-design -->
# System Test Plan: Backend Layer Artifact and Runtime Matrix

## Objective

Prove that the pure-Simple compiler publishes meaningful artifacts at every
shared and backend layer, executes the deepest applicable layer in each declared
environment, and accounts for every matrix cell without silent omission.

## Planned executable and manual artifacts

- Executable system spec:
  `test/03_system/compiler/backend/backend_layer_artifact_matrix_spec.spl`
- Generated manual:
  `doc/06_spec/03_system/compiler/backend/backend_layer_artifact_matrix_spec.md`
- Machine evidence root:
  `build/test-artifacts/03_system/compiler/backend/backend_layer_artifact_matrix_spec/`

The implementation phase must generate the manual with zero stubs and run the
SSpec maintenance scan. This documentation-only design phase does not create a
placeholder executable spec.

## Existing focused evidence

| Spec/check | Current evidence | Gap |
|---|---|---|
| `test/01_unit/compiler/backend/backend_stage_artifact_contract_spec.spl` | Contract validation/sink unit coverage exists | No measured 95% branch report |
| `test/01_unit/app/compile/backend_debug_dump_cli_spec.spl` | 4 examples, 0 failures | Does not detect successful silent omission after parsing |
| `test/02_integration/compiler/backend_debug_dump_driver_spec.spl` | Real source, AST, HIR, monomorphized HIR, and MIR artifacts observed | Timed out before optimized MIR; no backend stages |
| driver module check | Passed | Static check is not runtime evidence |

No test is rerun by this plan. The next implementation session starts from the
recorded evidence and uses the final corrected integration spec with a suitable
outer timeout once.

## Primary scenario flow

1. `step("select all compiler artifact stages")`
2. `step("compile the layered backend fixture")`
3. `step("validate every emitted compiler layer")`
4. `step("execute the deepest available backend layer")`
5. `step("account for the complete backend environment matrix")`

The generated manual shows the primary flow and links artifact/ledger captures.
Detailed backend rows and negative/fault-injection cases are folded by policy.

## Test levels

### Unit tests

- stage-list parsing: split/inline, `all`, empty, unknown, duplicate, dir-only;
- artifact metadata, safe paths, payload/path forms, digest and size mismatch;
- capability registry aliases, duplicates, inventory disagreement, formats;
- requested-stage tracker success and missing-stage failure;
- probe/result invariants and all matrix cell statuses;
- ledger product/completeness, duplicate/missing/stale cells;
- scheduler dependency, fail-fast, collect-all, and retry invalidation branches.

I/O and tool faults use injectable facades. Tests must not induce failures by
changing global developer tools or devices.

### Integration tests

- real multi-module pure-Simple compile across all six shared stages;
- `--debug-dump=all` fails explicitly until all applicable backend hooks emit;
- per-adapter meaningful IR validation plus object/link validation;
- deterministic repeat build and tamper detection;
- real process, runtime, emulator, simulator, or device readback receipt;
- unavailable probe versus present-but-invalid generated code classification.

### System/environment tests

The matrix runner executes one registry-derived plan per environment profile and
publishes a validated ledger. Cross-compilation proves generation only; the
run/readback cell runs natively or through the declared emulator/device.

## Canonical backend matrix

All ten stage columns appear in the actual ledger. This compact table describes
the deepest intended proof and special oracle.

| Canonical row/family | Required generated proof | Deepest proof |
|---|---|---|
| llvm-lib / LLVM | parse or verify LLVM IR/bitcode; inspect object | linked execution |
| Cranelift / native assembly | validate CLIF/assembly and object | linked execution |
| C++20 codegen | compile generated source and inspect object | linked execution |
| Wasm | validate WAT/wasm module | exported-function runtime result |
| CUDA/PTX | validate PTX/module | device buffer readback |
| HIP | validate generated module | device buffer readback |
| OpenCL | compile kernel/module | device buffer readback |
| Vulkan/SPIR-V | SPIR-V validation | fence plus buffer/image readback |
| Metal/MSL | compile MSL/metallib | command-buffer readback |
| VHDL | analyze and elaborate design | simulator output |
| BYL/SDN/Lua/Lean/interpreter/IRTC/legacy selectors | parse generated representation | tool/interpreter result |
| bare-metal x86/AArch64/RISC-V | inspect object/ELF/image | emulator/hardware receipt |

Registry discovery may add rows. Any discovered row absent from this plan must
fail inventory validation until its oracle is reviewed and added.

## Environment matrix

| Profile | Required baseline | Conditional rows |
|---|---|---|
| Linux x86_64 | six shared stages; available CPU backends; C; Wasm | CUDA/HIP/OpenCL/Vulkan on designated runners |
| Linux AArch64 | shared stages and native CPU generation/execution | available GPU/device rows |
| macOS AArch64 | shared stages, native CPU, C, Wasm, Metal | other available portable rows |
| Windows x86_64 | shared stages, native CPU, C, Wasm | CUDA/Vulkan when designated |
| FreeBSD x86_64 | shared stages and native CPU/C | portable available rows |
| SimpleOS/QEMU AArch64 | shared/cross generation, image, QEMU receipt | N/A only by capability declaration |
| SimpleOS/QEMU RISC-V | shared/cross generation, image, QEMU receipt | N/A only by capability declaration |

## Content oracles

- Source bytes equal the fixture.
- AST/HIR contain real declarations and cross-module imports.
- Monomorphized HIR contains the concrete generic instance.
- MIR/optimized MIR parse and contain expected control flow; optimized MIR must
  satisfy semantics, not a brittle instruction-count assertion.
- Backend IR passes its native parser/verifier and contains entry/callee symbols.
- Object and linked artifacts pass platform format inspection and target checks.
- Runtime/device receipts contain expected scalar or buffer output and matching
  producer/tool/device identities.

File existence alone is never the oracle.

## Negative and robustness cases

- `--debug-dump=all` with any unhooked requested stage;
- sink directory creation, write, copy, move, size, and digest failures;
- output root traversal and sanitized-name collisions;
- malformed IR, wrong target object, link failure, loader failure;
- unavailable tool/device, probe identity change after caching, launch timeout;
- device dispatch completion with incorrect readback;
- missing, duplicate, unknown, stale, or contradictory ledger cells;
- collect-all with failures in independent backends and dependency chains;
- retry where source, producer, target, tool, or device invalidates prior cache.

## Requirement traceability

| Requirement | Planned evidence |
|---|---|
| REQ-001 | parser unit matrix and CLI errors |
| REQ-002 | shared six-stage real integration scenario |
| REQ-003 | registry adapter integration rows |
| REQ-004 | process/device/emulator/simulator receipt scenarios |
| REQ-005 | outcome classification and required-profile tests |
| REQ-006 | sink integrity, tamper, path, and metadata tests |
| REQ-007 | repeat comparison and localized injected failures |
| REQ-008 | complete-ledger unit and environment system gates |
| REQ-009 | fail-fast, collect-all, and retry scenarios |
| REQ-010 | boundary-specific artifact/diagnostic assertions |

## Coverage and completion gates

- at least 95% reachable branch coverage for owned contract/registry/runner/
  adapters/probes, with reviewed exclusions;
- exactly 100% matrix accounting;
- no required `FAIL`, `SKIP_UNAVAILABLE`, missing, duplicate, or stale cell;
- two-run deterministic text/digest comparison passes;
- disabled instrumentation cost and resource/progress NFRs pass;
- `--debug-dump=all` cannot succeed while four backend stages are omitted;
- generated manual is readable, mirrors the executable spec, and has zero stubs.

## Stop policy

Run each acceptance gate once per implementation session. Use at most three
verify/fix cycles. After the third, publish the ledger and remaining failed cells
rather than restarting the complete matrix.
