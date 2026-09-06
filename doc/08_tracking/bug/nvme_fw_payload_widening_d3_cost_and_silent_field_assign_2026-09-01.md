# NVMe FW payload widening (D1-D3): measured cost regression + a silent-field-assign hazard

Filed 2026-09-01 while landing D1-D3 of
`doc/03_plan/hardware/nvme_command_set_and_payload_completeness_plan.md`
(payload widening, `examples/09_embedded/simpleos_nvme_fw/fw/`).
Both items below are recorded rather than fixed in that change; neither is a
test failure — all 33 `fw/*_check.spl` gates plus `test_fw.spl` are green.

## 1. Cost regression: `test_fw.spl` 1.30s -> 6.57s, RSS -> ~620 MB

Measured on `bin/simple` (Rust seed), same box, back to back:

| run | wall | max RSS |
|---|---|---|
| `test_fw.spl` before D3 | 1.30s | (not captured) |
| `test_fw.spl` after D3 | 6.57s | 620,620 kB |
| `nvme_emu_media_check.spl` before | 1.32s | — |
| `nvme_emu_media_check.spl` after | 1.82s | 168,468 kB |

**Cause is intended, the magnitude is the finding.** D3 replaces one `i64` per
NAND page with a real `PageData` of `PAGE_WORDS = 512` words, in BOTH behavioural
backends. Each backend allocates `NUM_PAGES * PAGE_WORDS` = 4096 * 512 = 2,097,152
words, and `test_fw.spl` constructs several devices. A 512x payload widening
costing ~5x wall and ~0.6 GB is proportionate, not a bug in the change — but it
is a real budget shift and it will grow as D4-D10 widen ECC, RAIN, FTL and DRAM
on top of it.

Watch items for the later commits:
- `erase_block` now writes `PAGES_PER_BLOCK * PAGE_WORDS` = 32,768 words per
  erase. GC-heavy lanes (`gc_safety_check.spl`, `durability_check.spl`) are the
  first place this will bite.
- Value semantics: every `NandRead`/`PageData` returned by value is a 512-word
  copy. D1-D3 keep all mutation on the single owner path
  (`me.page[ppn] = ...`, `me.oob[ppn].<field> = ...`) and never bind-mutate-write-back;
  a single aliasing slip here is a 4096x copy, per `.claude/rules/code-style.md`.
- If a later wave makes a gate unacceptably slow, the fix is a sparser page
  representation, NOT narrowing the profile constants back — the whole point of
  workstream D is that `PAGE_BYTES = 4096` stops being decorative.

## 2. Hazard: assigning to a renamed/nonexistent struct field is silently accepted

Hit directly during D3. `fil_nand.spl`'s selftest truncates the media array to
prove the fail-closed paths:

```
    var nt = nand_new()
    nt.data = []          # field was renamed to `nt.page` by D3
```

After the rename, `nt.data = []` did **not** error. It was accepted and did
nothing, so the truncation never happened and the assertion downstream failed
with a confusing `expected 2 got 0` instead of pointing at the stale field name.
A struct-field write to a name the struct does not declare should be a
compile-time error; silently swallowing it turns every field rename into a
silent test-weakening.

Impact beyond this example: any rename of a struct field can leave a
`x.old_name = ...` write in a test that now asserts nothing, with no diagnostic.
That is the same class of failure the repo's fail-closed guard convention exists
to prevent.

Reproduce: rename any struct field in a `.spl` file and leave one assignment to
the old name; observe no error from `bin/simple run`.

Not fixed here — the compiler is out of this change's scope
(`examples/09_embedded/simpleos_nvme_fw/fw/*.spl` only). The specific instance
was repaired by renaming the reference to `nt.page`, and the assertion it guards
is unchanged.
