# Bug: rv64_memory_ops_spec imports a module/class that was never implemented

- **Status:** open
- **Filed:** 2026-07-20
- **Affected spec:** `test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl`
- **Command:**
  `SIMPLE_RUST_SEED_WARNING=0 timeout 25 bin/release/x86_64-unknown-linux-gnu/simple test test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl --no-session-daemon`
- **Result:** `error: semantic: Cannot resolve module: hardware.rv64gc.mem.rv64_ram.Rv64Ram` → `error: test-runner: no examples executed`

## Symptom

The spec does `use hardware.rv64gc.mem.rv64_ram.Rv64Ram` and exercises a
byte-addressable RAM API: `Rv64Ram.create(size)`, `.write8/16/32/64(addr, value)`,
`.read8/16/32/64(addr).value` (load/store variants LB/LH/LW/LD/LBU/LHU/LWU,
SB/SH/SW/SD with sign/zero extension, covering 40+ examples across the file).

## Root cause

`grep -rln "class Rv64Ram" src/` and `grep -rln "fn write8\|fn read8"
src/lib/hardware/` both return **zero hits**. There is no
`src/lib/hardware/rv64gc/mem/` directory at all —
`find src -ipath "*rv64gc*" -name "*.spl"` lists only `rv64gc/__init__.spl`,
`rv64gc/mod.spl`, `rv64gc/top/{__init__,mod,rv64_machine}.spl`, and the
`rv64gc_rtl/` RTL modules (`alu`, `atomics`, `core`, `csr`, `csr_s`, `decode`,
`lsu`, `mmu_sv39`, `mul_div`, `pkg`, `regfile`, `trap`) — none of which expose a
standalone byte-addressable RAM class with this `create`/`write8`/`read8().value`
shape. `lsu.spl` (load-store unit) is the closest conceptual match but is RTL
signal-level, not this test's object API.

This is not a rename — no equivalent class exists anywhere to redirect the
import to. Either `Rv64Ram` needs to be implemented (likely under
`src/lib/hardware/rv64gc/mem/rv64_ram.spl`) or this spec predates a design
change where the LSU absorbed direct memory access differently and the test
was never migrated/removed.

## Repro (trimmed)

```
use hardware.rv64gc.mem.rv64_ram.Rv64Ram
var ram = Rv64Ram.create(16)
ram.write8(0, 0xAB)
expect(ram.read8(0).value).to_equal(0xAB)
```

Not touched: `test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl` left as-is (no
implementation exists to rename the import to; also note the file has a stray
`# tag: only-compiled` **comment**, not an actual `tag:` clause on `describe`,
so that comment plays no role in the failure and was left alone).
