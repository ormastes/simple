# V8 combined Zmmul + Zicsr system-test plan

## Status

**BLOCKED — qualification prerequisite unavailable.** Source-level structural
evidence exists; it is not a self-hosted or GHDL PASS.

## Scope and requirements

| Requirement | Evidence target |
| --- | --- |
| REQ-G2-013 | Combined RV32/RV64 V8 construction, direct product closure, strict VHDL route |
| REQ-G2-016 | Class-6/tag-3 CSR owner, frozen lookup/commit ABI, CSR capture and completion wiring |
| NFR-G2-003 | Repeated strict lowering produces identical graph receipt and VHDL |

The product is limited to `rv32i_zmmul_zicsr_zifencei` and
`rv64i_zmmul_zicsr_zifencei`.  IM, DIV, and REM are negative scope: their
absence must remain observable through rejected profile construction.

## Executable lanes

1. Structural system specification:
   `test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v8_csr_spec.spl`.
   It checks combined profile construction, tag-three/class-six routing,
   CSR-service ports, deterministic lowering, and IM/standalone-Zicsr
   rejection.
2. Clocked integration specification:
   `test/02_integration/compiler/riscv_scalar_runtime_pipeline_v8_flat_clocked_ghdl_spec.spl`.
   It is the behavioral lane for RV32/RV64 CSR capture, held completion,
   policy trap/no-commit, reset, and exact-once completion/commit behavior.

## Admission gate and resume

Do not run these as qualifying evidence through a Rust bootstrap seed.  The
gate is an admitted, executable pure-Simple binary at
`bin/release/x86_64-unknown-linux-gnu/simple`, plus a callable GHDL toolchain.
When both are available, execute exactly:

```sh
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v8_csr_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test test/02_integration/compiler/riscv_scalar_runtime_pipeline_v8_flat_clocked_ghdl_spec.spl --mode=interpreter
```

Record each result once.  A failure is a qualification failure; a missing
admitted binary or GHDL is BLOCKED, not PASS.
