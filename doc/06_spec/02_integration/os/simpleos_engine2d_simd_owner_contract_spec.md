# SimpleOS Engine2D SIMD Production Owners

## Scenario: inspect the production owner graph

1. Read the common noalloc evidence contract.
2. Read the x86_64 AVX2/SSE4.2, AArch64 NEON, and RV64 RVV owner modules.
3. Confirm each owner calls target intrinsics for fill, copy, alpha,
   alpha-edge, scroll, and diagram.
4. Confirm the compositor adapter selects only the compile-time target owner.
5. Confirm RVV contains no disabled placeholder or scalar-PASS path.

## Scenario: classify local source readiness

Run:

```sh
sh scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs --source-contract
```

The result must be `local-complete` with the external-only blocker
`external-qemu-execution-framebuffer-parity-and-guest-elf-disassembly-required`.
The normal checker mode cross-compiles and disassembles the three freestanding
intrinsic-owner objects, requires all six exported operation symbols plus
feature/width/metric symbols, and checks AVX/SSE, NEON, and RVV instructions.
The source-only mode does
not compile Simple, execute a guest, or launch QEMU. It cannot promote a SIMD
lane; linked guest-ELF instruction disassembly, positive guest hits, and exact
framebuffer parity remain mandatory external evidence.
## Local qualification status — 2026-07-28

The three architecture owners now expose all six operation ABIs. Alpha,
alpha-edge, and diagram execute SIMD arithmetic rather than transporting
vectors into a per-lane scalar blend. Their result is compared with an
independent scalar oracle. RV64 keeps the catalog/build baseline at `rv64gc`,
checks `misa.V`, reads `vlenb` only when V is present, and confines RVV to gated
inline-assembly blocks. The catalog QEMU CPU enables V with `vlen=128`.

Each x86_64, AArch64, and RV64 guest entry calls the shared render SIMD
qualification closure. The local checker proves compilation, the complete ABI
surface, target-appropriate instructions (decoding RVV with `--mattr=+v`
without changing object build flags), and source reachability. Local evidence
passes. A Simple-language guest link/build and live QEMU qualification receipt
remain external evidence requirements; neither is represented as passing here.
