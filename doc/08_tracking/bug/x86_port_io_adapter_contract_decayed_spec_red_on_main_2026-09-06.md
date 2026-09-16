# The x86 port-I/O adapter contract has decayed to one consumer; its spec is RED on `main`

**Filed:** 2026-09-06
**Severity:** medium — a landed architectural contract is unenforced and its spec has
been failing on `main`, so the decay was invisible
**Area:** `src/os/kernel/arch_adapt/x86_port_io.spl` and its declared consumers
**Spec:** `test/01_unit/os/kernel/arch/x86_port_io_arch_adapt_source_spec.spl`

## Measured state on `origin/main`

```
SPEC FILE VERDICT: ... outcome=ERROR declared>=2 executed=2 passed=1 failed=1
  ✓ is exactly the allocation-free whole-file forwarding contract
  ✗ routes every portable consumer only through the adapter
    expected false to equal true
```

The failing example asserts, for each of 9 declared portable consumers, that it
imports `os.kernel.arch_adapt.x86_port_io` and does NOT import the concrete owner
`os.kernel.arch.x86.port_io_owner`. Per-consumer, measured by grep on the
committed tree:

| consumer | adapter import | concrete import |
|---|---|---|
| `src/os/kernel/boot/cpu.spl` | **0** | 0 |
| `src/os/kernel/fw_cfg/x86_64_named_reader_v1.spl` | **DELETED** | — |
| `src/os/drivers/framebuffer/ramfb.spl` | **0** | 0 |
| `src/os/drivers/pci/pci.spl` | **0** | 0 |
| `src/os/drivers/rtc/rtc.spl` | **0** | 0 |
| `src/os/services/wm/wm_host_2d_simpleos.spl` | **0** | 0 |
| `src/os/sosix/io.spl` | **DELETED** | — |
| `src/os/sosix/io_rw.spl` | **0** | 0 |
| `src/os/test/desktop_e2e_test.spl` | 1 | 0 |

**2 of 9 consumers no longer exist, and 6 of the remaining 7 do not import the
adapter at all.** Exactly one consumer — a test file — still honours the
contract. Note the `concrete import` column is 0 everywhere: these files did not
bypass the adapter to reach the concrete owner, they stopped using this path
entirely.

## Why this was not caught

A first pass through this attributed the red to a single cause: `7df0aaba8c2`
("delete the dead Future chain and the unreachable sosix io.spl", landed via
PR #388) removed `src/os/sosix/io.spl`, which this spec reads as source text —
so the file was not "unreachable", a spec referenced it. That attribution is
**wrong, or rather one ninth of the story**: removing the three `sosix_io`
assertions was tried and the spec still fails 1/2, because eight other
assertions fail independently. Recorded here so the next person does not repeat
the same single-cause guess.

The deeper reason nothing caught the decay: this contract is enforced ONLY by
this spec, and the spec has been red, so each consumer that dropped the import
was landing against an already-failing check. A red gate stops ratcheting.

## What this is NOT

Not caused by the `port`/`dma` group ownership work: that lane measured this
spec at 1/2 with a byte-identical failure set on its pre-change tree.

## Repair options, none taken here

1. **Restore the contract** — re-add the adapter import to the 6 live consumers.
   Correct if the adapter is still the intended seam, but it is a 6-file change
   to OS boot/driver code with no gate currently proving it links or boots.
2. **Retire the contract** — if port I/O now legitimately routes through
   `port_io_owner` (see the `port` group ownership work), the adapter and this
   spec both describe a design that has been superseded, and the spec should be
   rewritten against the real seam rather than patched consumer by consumer.

Deciding between these needs the OS lane's owner. Removing assertions one at a
time until the spec goes green would convert a real architectural finding into a
green check, which is the failure mode this repo already documents for
`--generate-baseline`.
