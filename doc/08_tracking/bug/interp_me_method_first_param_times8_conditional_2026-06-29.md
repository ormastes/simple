# Bug: interpreter binds the first param of *some* multi-param `me` methods to value×8

**Filed:** 2026-06-29
**Status:** Open
**Affects:** `bin/simple run` (interpreter / Rust seed `me`-method argument binding). Compiled
paths untested here. **Conditional** — does not reproduce in isolation.

## Symptom
For certain multi-parameter `me` methods, the FIRST positional parameter binds to
`value × 8` (= `sizeof(i64)`) on method entry. The remaining parameters are correct.
Capturing the first param into a local on the first line does not help — it is already
`×8` when read, so the corruption is at parameter binding, not use.

Confirmed live in exactly one place so far: `examples/09_embedded/simpleos_nvme_fw/fw/ftl_journal.spl`,
method `append(map_lba, old_ppn, new_ppn, map_seq)`. With the natural 4-param signature,
`append(100, 10, 20, 1)` stores `wal_lba = 800`; the self-test catches it
(`record_lba(0)` expected 100, got 800).

## NOT universal — and not reproducible in isolation
Most multi-param `me` methods are unaffected (verified by round-trip self-tests):
`fil_nand.program(ppn,lba,seq,data)`, `fw_pool.acquire(cid,lba,nblk,data)`,
`fw_pool.set_ppns(h,old,new,seq)` all round-trip every param correctly. Minimal repros that
mirror `append`'s shape do **not** reproduce the ×8:
- `me poke(idx, v)` with `me.a[idx]=v` → correct (first param as index).
- `me store4(v1,v2,v3,v4)` / `store5(...)` with `me.arr[me.cnt]=v1` → correct (first as value).
- `me s_local` (local before use), `me s_guard` (if-guard before use) → correct.
- An exact replica of `append` (struct with 4 `[i64]` fields of length 512 + cap/cnt scalars,
  same guard + `val slot` + four `me.aN[slot]=pN` stores) → **correct**.

So the trigger depends on something beyond method shape — likely the interpreter's
method-table / call-frame slot layout for the specific `impl` (e.g. the particular set and
order of methods in `Journal`). Single-parameter `me` methods are always unaffected.

## Repro (in context)
1. In `ftl_journal.spl`, change `me append(_p0, map_lba, old_ppn, new_ppn, map_seq)` to drop
   `_p0` and update the 3 self-test call sites to 4 args.
2. `bin/simple run` a harness calling `ftl_journal_selftest()` → 3 FAILs, each an lba `×8`.

## Workaround (applied)
Add a leading dummy `_p0: i64` param (callers pass `0`). The corrupted "first param" is then
a throwaway and the real args start at position 2. See `fw/CONVENTIONS.md`. The clean form
for new code is a single struct param (single-param `me` methods never trip the bug).

## Detection rule
Every multi-param `me` method's self-test must round-trip EACH stored parameter value, so a
`×8` corruption surfaces as a failed assertion rather than silent data corruption.

## Root-cause hypothesis
Off-by-`sizeof(i64)` in the interpreter's argument-slot addressing for `me` methods, gated by
a layout condition (method count/order in the `impl`, or field count) that shifts the first
arg's computed offset. Needs a seed-interpreter investigation + a reduced trigger.
