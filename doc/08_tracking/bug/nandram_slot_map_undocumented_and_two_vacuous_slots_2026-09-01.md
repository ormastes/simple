# `.nandram` slot map was undocumented; two slots are defective

**Date:** 2026-09-01
**Status:** OPEN (map documented; the two slot defects are unfixed)
**Area:** `examples/09_embedded/simpleos_nvme_fw/fw_rv32`
**Related:** `doc/03_plan/hardware/nvme_emu_first_increment_plan.md` §3,
`doc/09_report/nvme_fw_current_state_audit_2026-09-01.md` (P0-1)

## What was found

The `.nandram` region is 64 words. Firmware uses **49 distinct word indices
(0-48)**, plus index 64 as a deliberate out-of-region probe, across roughly 250
call sites in `fw_rv32/entry.spl`. A subset is also poked by
`tb_rv32_nvme_fw_in_loop.vhd` (`ram(G_NANDRAM_WORD + <int>)`) and by
`scripts/qemu/qemu_rv32_nvme_fw_in_loop.shs` (GDB writes at computed offsets).

**No layout documentation existed anywhere in the tree.** Every index was a
bare integer in all three languages, with no shared definition and no drift
detection. Renumbering a slot in `entry.spl` would leave the testbench
injecting a fault into the wrong field or reading a counter that had moved —
a test that keeps passing while measuring nothing.

Scope note: the prior estimate (in the increment plan, from the subset visible
in the testbench) was ~16 slots. The real figure is 49. Any plan sizing based
on 16 is wrong.

## Fixed by this change

`fw_rv32/nand_test_slots.spl` — names all 49 slots plus the OOB probe, with a
role tag (`inject` / `observe` / `state`) and a one-line semantic per slot.
Host-only; not in the boot-linked import graph, so the freestanding rv32 path
stays no-alloc and decoupled (same rule as `const_drift_check.spl`).

`fw_rv32/nand_slot_drift_check.spl` — invariants over the map: positional
density, in-region bounds, every index named, OOB probe genuinely out of
region, plus a `_self_test()`. Verified non-vacuous by two mutations, each with
a control proving the mutation landed:

| Mutation | Result |
|---|---|
| `NAND_SLOT_REMAPS` 24 -> 23 (duplicate index) | `FAIL: slot 24 (REMAPS) is not positional` |
| `NAND_SLOT_OOB_PROBE` 64 -> 50 (probe inside region) | `FAIL: OOB probe is inside the region — the bounds test is vacuous` |

Clean run: `checked 49 slots in a 64-word region, 0 drift`.

## Still open

### FINDING 1 — slots 23 and 24 are redundant

`entry.spl:712-713`:

```
_nand_ram_store(23, _nand_ram_load(23) + 1)
_nand_ram_store(24, _nand_ram_load(24) + 1)
```

Both are incremented on adjacent lines inside `_nand_ram_remap`, nowhere else,
and are asserted together at `:979` (`_nand_ram_load(23) != 1 or
_nand_ram_load(24) != 1`). They cannot diverge. Either one is dead and should
be deleted (freeing a word), or they were intended to count different events
(e.g. FCR attempts vs. successful remaps) and one increment is in the wrong
place — which would be a real counter bug. Provisionally named `FCR_COUNT` and
`REMAPS`; the `(?)` marker in the map records that this is unconfirmed.

### FINDING 2 — slot 31 is a vacuous evidence digit

`entry.spl:547` writes `_nand_ram_store(31, 1)` at startup. Nothing ever writes
it again. It is then emitted as an evidence digit (`:453`) and asserted at
`:985` (`_nand_ram_load(31) != 1` -> fail).

**That assertion cannot fail.** It reads back a constant the same function
wrote and never modified, so the check passes unconditionally and the emitted
digit carries no information. This is precisely the non-vacuity failure both
hardware plans gate against: a green marker that measures nothing.

Either wire slot 31 to the quantity it was meant to report, or delete the slot,
the digit, and the assertion. Do not leave it as a passing check.

## Unblock condition for the rest

Converting `entry.spl`'s ~250 call sites to the named constants, and generating
the `.env` / VHDL constant package for the testbench and shell scripts, is
**deliberately not done here**. Its regression proof is "all existing markers in
`check-rv32-nvme-nand-recovery.shs` still pass byte-identically", and that
requires the GHDL/QEMU lanes, which currently fail closed with
`refusing non-production Simple runtime: bin/release/x86_64-unknown-linux-gnu/simple`.
Doing a 250-site rename on *inferred* slot semantics while unable to run the
lane that would catch a mis-inference would manufacture exactly the
unverifiable green this record exists to prevent.

Unblocks when the bootstrap redeploy lands. See
`doc/09_report/emulation_infra_inventory_2026-09-01.md`.

## FINDING 3 (adjacent, pre-existing) — `const_drift_check.spl` does not run

Discovered while regression-testing the above. Running the command its own
docstring prescribes, from the repo root:

```
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/const_drift_check.spl
-> rc=1
error: cannot resolve import `fw.nvme_types`: module path segment `fw` not found
       (looked in examples/09_embedded/simpleos_nvme_fw/fw_rv32/fw)
```

Confirmed pre-existing, not caused by the change in this record: the identical
failure reproduces with the only edited file (`fw/fil_nand_emu.spl`) stashed,
and that file is not in `const_drift_check`'s import graph.

This matters beyond the error itself. `const_drift_check.spl` is the repo's
model drift oracle — the file whose docstring explains why a regression oracle
is not a drift oracle, and which `nand_slot_drift_check.spl` was patterned on.
It is currently not executing, so the LBA_COUNT / NUM_BLOCKS / PAGES_PER_BLOCK
drift it exists to catch is unguarded. `ipc_drift_check.spl` runs fine
(`IPC DRIFT CHECK PASS`), so this is specific to the `fw.` import, not to the
drift-check pattern.

Needs its own fix; not in scope here.
