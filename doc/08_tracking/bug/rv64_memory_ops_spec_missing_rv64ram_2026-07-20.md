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

## Re-triage 2026-08-17 (content-classified, m9a_tests lane)

**Verdict: LIVE — the import target does not exist anywhere in the tree.**

`test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl` imports
`hardware.rv64gc.mem.rv64_ram.Rv64Ram`. Searched exhaustively:

- `find src -name rv64_ram* -o -name Rv64Ram*` -> **no hits**
- `grep -rn "Rv64Ram" src --include=*.spl` -> **no hits**
- `find src -path *rv64gc* -type d` -> only `src/lib/hardware/rv64gc`,
  `src/lib/hardware/rv64gc/top`, `src/lib/hardware/rv64gc_rtl`

`src/lib/hardware/rv64gc/` contains exactly `__init__.spl`, `mod.spl` and
`top/`. There is **no `mem/` subdirectory** and no `Rv64Ram` type under any
name. The PATH DRIFT annotation in the triage row is therefore not drift: the
module was never implemented, under this or any other path.

Because an unresolved `use` is only a WARNing, the spec loads with the symbol
missing and yields **zero examples executed** — a vacuous green, exactly the
class this batch targets.

Runtime confirmation attempt: `bin/simple test test/unit/hardware/rv64gc/rv64_memory_ops_spec.spl --timeout 1200`
was **SIGTERMed (rc=143, "Terminated") with no `Results:` line emitted** under a
host load average of 81-133. Per the session brief that is UNVERIFIED, not
failed, so no `Results:` line is quoted here. The content evidence above stands
on its own and does not depend on that run.
