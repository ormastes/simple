# Lane SPECFIX — spec matcher repair (canonical `expect(X).to_matcher(Y)`)

- Date: 2026-07-27
- Related bug: `doc/08_tracking/bug/spec_matcher_nested_call_dispatch_2026-07-27.md`
- Binary used: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`
  (emits the *bootstrap-seed* warning banner — evidence is SEED evidence).
- Verification command: `bin/simple run <spec>` (never whole-suite `simple test`).
  One `N examples, M failures` line per describe block; blocks listed in order.

## Scope

Enumerated with the bug-report regex (`build/specfix_sites.txt`):

```
grep -rnE '[A-Za-z0-9_\]\)]\.[A-Za-z0-9_]+\([^()]*\)\.to_(equal|be|contain|include|start_with|end_with|not_)' \
  --include='*_spec.spl' test/ src/
```

**160 sites / 25 tracked spec files** (the bug report's "173 / 27" counted the
generated, untracked `test/01_unit/os/kernel/loader/.spipe_matchers_smf_spec.spl`
cache artifact too). All 160 were `.to_equal(`; no other matcher appeared in the
chained shape.

Shape breakdown of the 160:

| shape | count | note |
|---|---|---|
| bare — no `expect` at all | 127 | asserted nothing / hard-errored |
| paren-less `expect X.m().to_equal(Y)` | 33 | parses as `expect(X.m().to_equal(Y))` |
| `expect(...)` double-matcher chain | 5 | 3 real + 2 duplicate-tree copies |

The bug report says only `disk_boot_spec.spl:121` lacked an `expect`. That is
wrong by two orders of magnitude — **127 of the 160 sites had no `expect`**,
including all 31 of `per_target_build_spec.spl` and all 15 of
`cross_build_plan_spec.spl`.

Duplicate trees: `test/unit`, `test/system`, `test/integration` are real,
git-tracked, byte-duplicated copies of `test/01_unit`, `test/03_system`,
`test/02_integration` (separate inodes, both tracked). Both copies were fixed.

`test/01_unit/lib/ecs/ecs_spec.spl` deliberately untouched (owned by lane ECSGEN).

## Conversion rule (mechanical only)

1. `expect(X.m(a).to_equal(Y))` -> `expect(X.m(a)).to_equal(Y)`
2. `expect X.m(a).to_equal(Y)`  -> `expect(X.m(a)).to_equal(Y)`
3. `X.m(a).to_equal(Y)`         -> `expect(X.m(a)).to_equal(Y)`

Nothing about *what* is asserted changed. Every changed line was diffed 1:1
against a pre-edit backup in `build/specfix_bak/`; paren balance verified on
every `+` line.

Two double-matcher chains had no direct canonical equivalent (there is no
negating matcher in the runner's table) and were rewritten to a comparison that
preserves the asserted meaning exactly:

- `expect(name).to_equal("").to_equal(false)` -> `expect(name == "").to_equal(false)`
- `expect(args).to_be_nil().to_equal(false)`  -> `expect(args == nil).to_equal(false)`

Probe (`build/specfix_probe`, deleted): `xs == nil` and `name == ""` both work
under `expect(...)`. `expect(xs.?).to_equal(true)` does **not** — `.?` on a list
yields the list itself, so the matcher reports `expected [1, 2] to equal true`.
That is a separate defect worth filing.

## Results table

Verdicts are `examples/failures` per describe block, in block order.

| file | sites | BEFORE | AFTER | delta |
|---|---|---|---|---|
| test/01_unit/lib/crypto/ml_kem_768_kat_spec.spl | 21 | 5/3 ; 4/0 ; 2/2 | **5/0** ; 4/0 ; 2/2 | +3 real passes |
| test/unit/lib/crypto/ml_kem_768_kat_spec.spl | 21 | (same file content) | same as above | +3 |
| test/01_unit/lib/viz/frame_builder_spec.spl | 5 | 7/5 | **7/0** | +5 |
| test/unit/lib/viz/frame_builder_spec.spl | 5 | 7/5 | **7/0** | +5 |
| test/01_unit/lib/viz/frame_scheduler_spec.spl | 4 | 7/3 | **7/0** | +3 |
| test/unit/lib/viz/frame_scheduler_spec.spl | 4 | 7/3 | **7/0** | +3 |
| test/unit/lib/ecs/ecs_spec.spl | 13 | 4/3 ; 3/2 (3rd block never reported) | **4/0 ; 3/0 ; 2/0** | +5, 3rd block recovered |
| test/unit/os/kernel/loader/smf_spec.spl | 5 | 3/0 ; 3/2 ; 7/2 | 3/0 ; 3/2 ; **7/0** | +2 |
| test/01_unit/sffi/sffi_public_api_spec.spl | 1 | 2/0 ; 2/2 ; 2/2 ; 2/0 | 2/0 ; **2/0** ; 2/2 ; 2/2 ; 2/0 | +2, 5th block recovered |
| test/unit/sffi/sffi_public_api_spec.spl | 1 | same | same | +2 |
| test/01_unit/os/kernel/loader/elf64_spec.spl | 2 | 4/2 | 4/2 | 0 — blocked, see F1 |
| test/unit/os/kernel/loader/elf64_spec.spl | 2 | 4/2 | 4/2 | 0 — F1 |
| test/unit/os/kernel/smp/smp_spec.spl | 1 | 4/4 ; 4/4 | 4/4 ; 4/4 | 0 — blocked, see F3 |
| test/integration/os/port/llvm/per_target_build_spec.spl | 31 | 21/21 | 21/21 | 0 — blocked, see F2 |
| test/integration/os/port/llvm/cross_build_plan_spec.spl | 15 | 14/14 | 14/14 | 0 — F2 |
| test/integration/os/port/rust/smoke_rustc_spec.spl | 3 | 4/3 | 4/3 | 0 — F2 |
| test/02_integration/os/port/rust/smoke_rustc_spec.spl | 3 | 4/3 | 4/3 | 0 — F2 |
| test/integration/os/port/llvm/smoke_clang_spec.spl | 5 | 5/0 | 5/0 | 0 (env-skipped) |
| test/system/os/port/disk_boot_spec.spl | 4 | 5/0 | 5/0 | 0 (env-skipped) |
| test/03_system/os/port/disk_boot_spec.spl | 4 | 5/0 | 5/0 | 0 (env-skipped) |
| test/system/os/port/e2e_qemu_smoke_spec.spl | 1 | 6/0 | 6/0 | 0 |
| test/03_system/os/port/e2e_qemu_smoke_spec.spl | 1 | 6/0 | 6/0 | 0 |
| test/01_unit/app/ui/display_detect_spec.spl | 1 | load error | load error | 0 — pre-existing, see F4 |
| test/unit/app/ui/display_detect_spec.spl | 1 | load error | load error | 0 — F4 |

**Not converted (deliberate):**

- `test/01_unit/lib/test_runner_native_spipe_preprocess_spec.spl:126` — the
  chained matcher is *inside a string literal* written to a temp file as a
  fixture the preprocessor must reject. Converting it would break the test.
- `test/01_unit/os/kernel/loader/.spipe_matchers_smf_spec.spl` — untracked
  generated cache artifact; regenerates from `smf_spec.spl`.
- `test/01_unit/lib/ecs/ecs_spec.spl` — lane ECSGEN.

**Zero regressions.** No file's failure count increased. **24 files converted**
(all tracked files carrying a site, minus the deliberate string-literal fixture
and the ECSGEN-owned file). The pass is complete, not partial.

## Newly revealed genuine failures

None. Every example that was red before and is still red is red for a
*pre-existing, unrelated* reason (each verified by running the pre-edit backup
from `build/specfix_bak/` and comparing failure messages verbatim). Conversion
did not expose any new product defect — it converted 33 previously-erroring
examples into genuine passes, which is the opposite outcome, but it did expose
the four latent blockers below that were being masked by the matcher error.

### F1 — `is_nil()` unresolvable on `Option` / struct receivers (same dispatcher family)

`test/{01_unit,unit}/os/kernel/loader/elf64_spec.spl`,
`test/unit/os/kernel/loader/smf_spec.spl` block 2:

```
semantic: method `is_nil` not found on type `enum` (receiver value: Option::None)
semantic: method `is_nil` not found on type `SmfHeader`
```

Pre-existing (identical before conversion). This is the *same* under-populated
nested-call dispatcher as the matcher bug, but for `is_nil` rather than the BDD
matchers, so fixing `call_method_on_value` per the bug's fix sketch will not
cover it. Worth folding into that bug.

### F2 — `use std.fs` namespace resolves to a `dict`, so `fs.*` methods vanish

`per_target_build_spec.spl` (21/21), `cross_build_plan_spec.spl` (14/14),
`smoke_rustc_spec.spl` (3 of 4):

```
semantic: method `read_to_text` not found on type `dict`
  (receiver value: {Path__components: <fn:...>, resolve: <fn:...>, ...})
semantic: method `exists` not found on type `dict`
```

Pre-existing and total: **36 examples across 4 files are red purely because the
`fs` module namespace object is being treated as a plain dict.** Accompanied by
`[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
Unknown variable: fs`. These specs assert nothing today regardless of matcher
shape. This is the single largest coverage hole this lane found and it is a
compiler/stdlib defect, not a test defect — needs its own bug.

### F3 — `smp_spec.spl` per-CPU array indexed out of bounds

Both trees, all 8 examples across 2 blocks:

```
semantic: array index out of bounds: index is 1 but length is 1
```

Pre-existing. The per-CPU table is allocated with length 1 but the spec brings a
second CPU online. Real product-or-fixture defect, unrelated to matchers.

### F4 — `display_detect_spec.spl` cannot resolve its module

```
error: semantic: Cannot resolve module: common.test_runner.display_detect
```

Pre-existing; the file never loads, so no example ever runs. Note it uses
`use common.test_runner...` rather than the `use std.X` convention.

### F5 — stale committed probe block in `ml_kem_768_kat_spec.spl`

Lines 125-132 of both copies carry:

```
# W12-A PROBE — DO NOT COMMIT (will be reverted)
describe "W12-A probe — postfix value.to_equal":
```

It contains two examples that assert `3329 == 99999` and `1 == 99999`, i.e. they
are *designed* to fail, and they were committed anyway. This is the entire
remaining `2 examples, 2 failures` block on that file. Not deleted here (out of
this lane's mandate to change what is asserted) — the owner should delete it.

### F6 — `.?` presence operator is a no-op on lists

`expect(xs.?).to_equal(true)` reports `expected [1, 2] to equal true` — the
operator yields the receiver rather than a bool. Found while choosing a
replacement for the `to_be_nil().to_equal(false)` chain. Matches the known
"`.?` on 0-i64 -> false" family in memory. Use `x == nil` instead.

## Scale finding beyond this lane

The paren-less `expect X ...` form (the outer-`expect`-degrades-to-truthiness
hazard) is not 33 sites — it is **29,875 sites across the tracked spec corpus**
(`build/specfix_parenless.txt`). It only *breaks* when a matcher is chained onto
a method call (the 160 fixed here); otherwise it merely degrades the failure
message from `expected 1 to equal 2` to `expected call result to be truthy, got
false`. A repo-wide normalisation is a separate, much larger campaign and was
deliberately not attempted.

## LANDMINE — a parallel session reverted the whole working tree mid-lane

At 22:44:40 every one of the 24 converted spec files was rewritten back to its
original byte size by another session (the known "sync sweeps agent scratch
state" / "stale WC reverts pushed fixes" failure mode). It was caught only
because a post-hoc re-run of `test/unit/lib/crypto/ml_kem_768_kat_spec.spl`
still reported the *old* `5 examples, 3 failures` — the residual-site grep had
already reported clean before the revert, so the grep alone would have hidden it.

The conversion was re-applied deterministically from
`build/specfix_filelist.txt` and **every verdict in the table above was
reproduced identically** on the re-run. If this state file is read after another
such revert, re-verify with:

```
grep -rnE '[A-Za-z0-9_\]\)]\.[A-Za-z0-9_]+\([^()]*\)\.to_(equal|be|contain)' \
  --include='*_spec.spl' test/ | grep -v spipe_matchers
```

Only `test/01_unit/lib/test_runner_native_spipe_preprocess_spec.spl:126` should
match. Anything else means the lane was reverted again.

Lesson: after a sed/Edit sweep, re-run at least one converted spec and confirm
the *verdict* changed, not just that the grep is clean. A clean grep taken
before the clobber is worthless evidence.

## Artifacts

- `build/specfix_sites.txt` — the 160 enumerated sites
- `build/specfix_files.txt` — per-file site counts
- `build/specfix_parenless.txt` — the 29,875 paren-less sites (scale evidence)
- `build/specfix_bak/` — pre-edit backups used for every A/B
- `build/specfix_filelist.txt` — the 24 files converted (re-apply list)
- `build/specfix_b_*.txt`, `build/specfix_a_*.txt` — before/after run logs
