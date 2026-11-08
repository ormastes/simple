# The acpi unit spec's three positive reads return 0, and it is NOT the nested-fn capture defect it was attributed to

- **id:** acpi_spec_three_reads_return_zero_2026-09-19
- **status:** OPEN — undiagnosed, needs an owner
- **severity:** P2 — a red in the phase-1 unit suite with no current owner
- **found:** 2026-09-19, while fixing
  `nested_fn_in_spec_block_loses_captured_local_2026-08-04`

## Symptom

`test/01_unit/os/acpi/acpi_test.spl`, 10 examples, 3 fail. Same three, with the
same numbers, on every binary tried:

```
✗ extracts MMIO base from GAS address at offset 48   expected 0 to equal 4275044352
✗ reads legacy PM_TMR_BLK at offset 76 ...           expected 0 to equal 45064
✗ prefers X_PM_TMR_BLK GAS at offset 208 ...         expected 0 to equal 47104
```

Every failing example asserts a **non-zero** value and gets `0`. The three
passing siblings in the same groups all assert `nil`, which a zeroed read also
satisfies — so the spec's green examples do not discriminate, and the real
failure rate of whatever is broken may be higher than 3.

## Why it is filed separately

Since 2026-08-04 these three were recorded as the "silent zero" arm of
`nested_fn_in_spec_block_loses_captured_local`, on the strength of the shape:
each builds a `[u8]` fixture and hands `r8`/`r32` nested `fn`s to
`acpi_hpet_base_raw`. That attribution is wrong, and was disproved twice:

1. The nested-fn capture defect was fixed on 2026-09-19. **These three still fail
   identically** on the fixed binary.
2. A minimal probe of exactly this shape — a nested `fn` capturing a local
   `[u8]`, forwarding to a module-level `_buf_read32`, passed as a callback and
   called through — **passes on the OLD (unfixed) binary too**. The callback shape
   was never broken; only the direct-call shape was.

So whatever zeroes these reads is downstream of the callback, not in it.

## Where to look next, and what is already ruled out

Ruled out by the probe above: nested-`fn` capture of the fixture array; passing a
nested `fn` as an argument; a module-level `u32` assembler
(`b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)`) reading a captured buffer through a
callback — that combination returns `0xFED00000` correctly.

Not yet examined: `_make_hpet_table` / the FADT fixture builders (whether the
bytes are where the assertions think they are), `acpi_hpet_base_raw` and the FADT
parser themselves, and the `u8`/`u32`/`u64` conversions at the assertion boundary
(`expect(result as u64)`).

A cheap first step is to assert the fixture directly — read offset 48 out of
`_make_hpet_table(...)` in the spec and check the bytes — which separates a bad
fixture from a bad parser without touching either.

## Related

- `nested_fn_in_spec_block_loses_captured_local_2026-08-04.md` — the record that
  carried these three until now; its 2026-09-19 fix note records the measurement
  that separated them.


## 2026-11-03 source investigation (candidate; behavioral verification blocked)

Current release source was inspected at `074d5611e1dfb53286fb1acb2e3e457957047013`.
The pure reader owners are `src/os/kernel/acpi/hpet_table.spl` and
`src/os/kernel/acpi/fadt.spl`; both accept table-relative readers and deliberately
permit `base = 0`. FADT fixture writes and parser accesses agree at 76 and
208/212. No evidence attributes these failures to nested-function capture.

An independent production HPET layout defect was found: the code invented four
reserved bytes after EventTimerBlockID. The HPET specification 1.0a section 3.2.4
places the 12-byte GAS at byte 40, hence its address at byte 44. The parser and
fixture now use these standard offsets. Source reference:
[Intel HPET specification](https://www.intel.com/content/dam/www/public/us/en/documents/technical-specifications/software-developers-hpet-spec-1-0a.pdf).
This layout correction alone does **not** explain the historical zero result,
because the old fixture agreed with the old parser's wrong layout.

The three positive examples now assert fixture words before calling the parser,
and inspect the optional payload with `?? 0` before retaining the original
numeric cast assertion. A payload/cast disagreement can therefore identify the
assertion boundary without removing the reported failure operation. Adjacent
fixtures cover a nonzero high HPET address word and nonzero legacy fallback for
wrong-space/zero-address FADT extended GAS. No physical MMIO is accessed.

**TEST_BLOCKED:** no qualified self-hosted Simple CLI is available on this host;
`bin/simple.exe` is the bootstrap-only Rust seed. Zero behavioral examples were
executed. The 13 authored examples and their output/cast boundaries still require
execution through a qualified producer. This bug remains open; neither a hardware
PASS nor a diagnosis/closure of the historical three zero reads is claimed.

## 2026-11-09 diagnosis — root cause found, fix implemented (verification pending)

Executed against worktree source with `child binary: C:\dev\wt\acpi\bin\simple.exe`
(release/1.0.0 @ e954b1d95e2 + this change).

**Red (before):** 13 examples, 3 failed — the same three, same numbers
(`expected 0 to equal 4275044352 / 45064 / 47104`).

**Root cause is NOT in the ACPI parsers or fixtures.** In each failing example
the `expect(result ?? 0).to_equal(...)` assertion already PASSED; only the
trailing `expect(result as u64)` / `expect(result as u32)` line failed. The
sibling examples that use only `?? 0` (`preserves both HPET address words`,
both `falls back to a nonzero legacy port` cases) were green on the same run,
so `acpi_hpet_base_raw` and `acpi_fadt_pm_tmr_port_raw` return the correct
payloads.

The zero comes from applying `as <int>` to a `T?` value returned from a
function: the seed evaluates `Some(0xFED00000) as u64` to `0`. A spec-independent
probe reproduces it (`fn mk(v: u64) -> u64?` returning `v`; `mk(0xFED00000) as u64`
-> `0`, while `?? 0` -> `0xFED00000`; a locally-typed `val r: u32? = 0xB008; r as u32`
passes, so the defect is specific to the boxed/returned optional). Under the
nil-only-in-unsafe policy (`T?` -> `T` must go through `??`/unwrap), that cast
should be rejected at compile time, not silently zeroed — filed separately as
`optional_as_cast_yields_zero_2026_11_09`.

Why it looked like "three reads": the only positive-payload assertions in the
original spec were written with `as`, and the nil siblings cannot distinguish a
zeroing parser from a working one. The nested-fn attribution, the HPET GAS
offset (fixed in #6338), and the FADT 76/208 layout were all red herrings for
this symptom.

**Fix (spec):** drop every `as` cast on an optional; assert `to_not_be_nil()` and
`?? 0` payload separately; add a discriminating example that pairs a zero fixture
(nil) with a nonzero fixture (present) for both parsers.

**Green (after):** `SPEC FILE VERDICT: ... outcome=OK executed=14 passed=14 failed=0`.
Status: fix-implemented-verification-pending (interpreter run on the Windows seed;
native verification outstanding).
