# V7 unified dynamic IM owner system-test plan

## Status

Source-level structural V7 scenarios exist, but no qualifying V7 execution has
occurred. Qualification is blocked by the unavailable admitted self-hosted
Simple runtime. `ghdl` is callable on this host, but no admitted GHDL result
has been retained.

## Requirement mapping

| Requirement | Structural evidence | Clocked/GHDL evidence |
| --- | --- | --- |
| REQ-G2-012 | One tag-2 owner, one completion path, fault-gate wiring | held envelope, backpressure, exact-once consume, reset |
| REQ-G2-013 | exact RV32IM/RV64IM profile closure, all M rows, no V6 provider | arithmetic, special cases, W geometry, malformed metadata |
| NFR-G2-003 | repeated strict lowering has equal receipt and VHDL | same generated entity compiled/simulated by GHDL |

## Current executable lanes

1. `test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v7_im_spec.spl`
   constructs RV32IM and RV64IM V7 products, asserts one tag-2 M owner,
   reject Zmmul-only/Zicsr/combined profiles, check all M forms are represented,
   and compare two strict lowerings for identical receipt/VHDL.
2. `test/02_integration/compiler/riscv_scalar_runtime_m_provider_ghdl_spec.spl`
   renders and drives the flat M provider only. It covers reset, held
   completion, consume, malformed fault, RV32 DIV/REM, and RV64 M/W vectors;
   it is not a full V7 pipeline bench and lacks RV32 multiply vectors.

## Clocked matrix

| Family | RV32 vectors | RV64 vectors |
| --- | --- | --- |
| Multiply | MUL/MULH/MULHSU/MULHU; signed high-half and x0 | same plus MULW with hostile upper bits and sign extension |
| Divide | DIV/DIVU, negative signed operands, zero divisor, min/-1 | same full width plus DIVW/DIVUW hostile-upper-bit and sign-extension vectors |
| Remainder | REM/REMU, negative signed operands, zero divisor, min/-1 | same full width plus REMW/REMUW hostile-upper-bit and sign-extension vectors |
| Protocol | malformed row, semantic, width, raw binding, lineage, illegal marker | same, proving sticky fault and no completion |
| Temporal | at least one iterative cycle, ready low while busy, held completion, single consume, reset idle/busy/held | same |

Every normal completion must assert tag 2, original/canonical identity,
length 4, captured fallthrough PC, provider/decode event IDs, zero
memory/trap/redirect effects, and `rd_write == (rd != 0)`.

## Qualification gate

When a pure-Simple (not Rust bootstrap seed) executable exists at
`bin/release/x86_64-unknown-linux-gnu/simple` and GHDL is callable, run once:

```sh
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test test/03_system/app/hardware/feature/riscv_gen2_runtime_pipeline_v7_im_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test test/02_integration/compiler/riscv_scalar_runtime_m_provider_ghdl_spec.spl --mode=interpreter
```

These existing commands are development evidence only until the runtime is
admitted. Add a full-pipeline clocked GHDL scenario and RV32 multiply vectors
before using them for final qualification. Missing prerequisites are BLOCKED,
not PASS; bootstrap output is not a substitute. Record each lane once and do
not release on incomplete evidence.
