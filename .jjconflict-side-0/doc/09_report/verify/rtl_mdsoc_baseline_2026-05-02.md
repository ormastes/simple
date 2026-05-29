# RTL MDSOC Baseline (2026-05-02)

**Status: BLOCKED**

**Purpose:** AC-2 byte-equal oracle for `.sstack/rtl_riscv_mdsoc_reorg`. This file would contain
sha256 fingerprints of every artifact under `build/rtl_linux/` produced by the two generation
scripts, serving as the post-refactor bit-equality check for SA-2/3/4.

## Generation Status

| Lane | Script | Exit Code | Result |
|------|--------|-----------|--------|
| RV32 | `scripts/rtl_riscv32_linux_generated.shs` | 0 | **PASS** |
| RV64 | `scripts/rtl_riscv64_linux_generated.shs` | 126 | **FAIL** |

## RV32 Lane Output (PASS)

```
PASS: generated RV32 RTL Linux tools present
[generated_rv32_linux] proof gate: linux_handoff
[GHDL-GEN-RV32-LINUX-HANDOFF] PASS
[generated_rv32_linux] proof gate: real_dtb
[GHDL-GEN-RV32-BOOT-INFO-REAL-DTB] PASS
PASS: generated_rv32_linux generated Linux acceptance gates passed
```

## RV64 Lane Failure

```
PASS: generated RV64 RTL Linux tools present
scripts/rtl_riscv64_linux_generated.shs: 58: /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple: Exec format error
EXIT_CODE=126
```

**Root cause:** The RV64 lane's `prepare_payload()` function (line 58 of the script) invokes
`src/compiler_rust/target/debug/simple` to compile a RISC-V payload ELF. The binary at that
path is a stale/wrong-architecture Rust debug build and cannot execute on this host. This is
not a regression introduced by the `rtl_riscv_mdsoc_reorg` feature; it is a pre-existing
environment condition (debug binary not rebuilt for current host arch).

**Fix:** Rebuild the Rust seed: `cargo build` inside `src/compiler_rust/`, or use `bin/simple`
(the release binary) in the RV64 script's `prepare_payload` instead of the debug path.
This is out of SA-1 scope — escalate to the architect before SA-2/3/4 run.

## Secondary Finding: Ephemeral VHDL Artifact Paths

During investigation it was confirmed that both RV32 runner scripts generate VHDL files into
`mktemp -d /tmp/ghdl_*` directories (cleaned up with `trap "rm -rf $TMP_DIR" EXIT`). The
generated VHDL is **not** written to a stable path under `build/rtl_linux/`. Specifically:

- `ghdl_generated_rv32_linux_handoff_runner.shs` calls `bin/simple run generate_riscv_fpga_bundle.spl -- "$GEN_DIR"` where `GEN_DIR="$TMP_DIR/generated"` (temp)
- After GHDL simulation, `$TMP_DIR` is deleted — no durable `.vhd` or `.debug.json` artifacts remain

**Architecture gap:** AC-2's "byte-equal oracle" (sha256 of generated VHDL) requires durable
artifact paths. The Phase-3 architecture assumed `build/rtl_linux/generated_rv{32,64}/` would
contain the VHDL output, but the scripts leave no `.vhd` files there (only logs and ELFs for
RV64). Before SA-2/3/4 can validate byte-equality, the architect must either:
1. Modify the runner scripts to preserve generated VHDL in `build/rtl_linux/generated_rv{32,64}/rtl/`, or
2. Have SA-1 invoke `generate_riscv_fpga_bundle.spl` directly into a stable directory and use that as the oracle tree.

**This file will be regenerated with full sha256 + line-count tables once:**
1. The RV64 lane is fixed (Rust debug binary rebuilt or script updated to use release binary), AND
2. The artifact path is made durable (or oracle strategy is revised as above).

## How to Validate Post-Refactor (when unblocked)

1. Run both generation scripts:
   ```
   sh scripts/rtl_riscv32_linux_generated.shs
   sh scripts/rtl_riscv64_linux_generated.shs
   ```
2. Capture sha256 of every file in the stable artifact tree (TBD path after fix):
   ```
   find build/rtl_linux -type f | sort | xargs sha256sum
   ```
3. Compare against baseline tables in this file — diff must be empty.
4. Same for `.debug.json` sidecars (key-order fingerprint per AC-3).
