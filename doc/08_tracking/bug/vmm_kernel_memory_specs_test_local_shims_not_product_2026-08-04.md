# BUG: `test/01_unit/os/kernel/memory/` specs test spec-local copies, not `src/os/kernel/memory/` — and both copies share a real value-semantics defect

**Status:** FIXED
**Found:** 2026-08-04
**Fixed:** 2026-08-06
**Severity:** high — 31 failing examples, and the specs are **vacuous**: they
cannot observe the product module at all, so fixing `src/os/` would not turn
them green and a product regression would not turn them red.

## Fix summary (2026-08-06)

Implemented the sequencing recommended below, exactly. No branch — landed
directly on `main` per repo VCS rules.

### 1. Product fix: mutators now return the updated `ProcessVmSpace`

`src/os/kernel/memory/vmm_vma.spl` — three mutators had the by-value-struct
defect (mutate a local copy, return only an errno, or return nothing); one
(`vma_remove`) was already correct and served as the reference pattern.

| function | before | after |
|---|---|---|
| `vma_add` (`:78`, was `:64`) | `(space: ProcessVmSpace, area: VmArea) -> i32` | `(space: ProcessVmSpace, area: VmArea) -> VmaAddResult` (new struct `{code: i32, space: ProcessVmSpace}`) |
| `vma_split` (`:199`, was `:171`) | `(space: ProcessVmSpace, vaddr: u64) -> i32` | `(space: ProcessVmSpace, vaddr: u64) -> VmaSplitResult` (new struct `{code: i32, space: ProcessVmSpace}`) |
| `vmm_teardown_user_space` (`:174`, was `:153`) | `(space: ProcessVmSpace)` (void) | `(space: ProcessVmSpace) -> ProcessVmSpace` |
| `vma_remove` (`:96`) | unchanged — already `-> ProcessVmSpace`, used as the reference pattern | unchanged |

`vma_split` has **zero callers anywhere in the repo** (grep-confirmed) — fixed
for correctness/consistency with zero call-site risk.

### 2. Call sites updated

Full-repo grep for `vma_add(`, `vma_split(`, `vmm_teardown_user_space(` found
a **much smaller** live call-site set than the doc's ~39-file estimate (that
count was files merely *referencing* the `ProcessVmSpace` type, not calling
these three specific mutators):

- `vma_add`: exactly **one** caller, `vmm_mmap` (`vmm_vma.spl:326`) — updated
  to read `add_result.code` / (documented, not threaded further — see
  "Deliberately not fixed" below).
- `vma_split`: **zero** callers — no call sites to update.
- `vmm_teardown_user_space`: **3** call sites —
  `src/os/kernel/ipc/syscall_process.spl:311` (discards result via `_ =`,
  correct since the caller replaces the whole vmspace immediately after) and
  both copies of `execve_spec.spl`
  (`test/01_unit/os/kernel/ipc/execve_spec.spl`,
  `test/unit/os/kernel/ipc/execve_spec.spl` — genuine duplicate files, both
  updated identically) which now do `space = vmm_teardown_user_space(space)`.

### 3. Spec de-vacuation (the 4 target files)

| spec | shim removed | replaced with |
|---|---|---|
| `vmm_vma_spec.spl` | `_space_add`, `_vma_overlaps_local`, `_space_find` | `use os.kernel.memory.vmm_vma.{vma_add, vma_find, vma_remove, vma_split}` — all test bodies now call the real functions and thread the returned `.space` |
| `pmm_spec.spl` | `_TestPhysMemManager` struct+impl | `use os.kernel.memory.pmm.{PhysMemManager}` — real struct constructed directly (its methods are pure arithmetic over its own fields; only the separate `_bitmap_*` helpers touch mmio, out of scope per the file's own docstring) |
| `vmm_cow_spec.spl` | none (doc named none explicitly for this file) | see below — kept as a hardware-independent simulation (real `vmm_cow_clone_result` calls real page-table code via `vmm_cow_clone_pages`, untestable without a booted MMU), but its **own** local helpers had the identical by-value-struct bug and were fixed in place |
| `vmm_copyin_spec.spl` | none needed | already imported the real `os.kernel.memory.vmm` functions (the doc's "1 import" count) — no shim to remove |

`vmm_cow_spec.spl` detail: `_cow_space_add`, `_sim_ref`, `_sim_unref`,
`_sim_alloc`, and `_sim_cow_clone` all had the same by-value-struct-parameter
defect as the product bug (mutating `_SimPmm`/`ProcessVmSpace` locals that
were discarded on return). All five now return their updated struct
(`_sim_unref`/`_sim_alloc` via new `_SimUnrefResult`/`_SimAllocResult`;
`_sim_cow_clone` via `_SimCowResult{parent, child, pmm}`, mirroring the real
`VmmCowCloneResult{ok, parent, child}`), and all 10+ call sites were updated
to thread the returned value. This was judged in-scope (bounded, single-file,
same bug class) rather than a "separate defect to file" — see the task's own
bounded-effort framing.

### 4. Results

| spec | before | after |
|---|---|---|
| `vmm_vma_spec.spl` | 18 total, 7 passed, 11 failed | **18 total, 18 passed, 0 failed** |
| `vmm_cow_spec.spl` | 18 total, 5 passed, 13 failed | **18 total, 18 passed, 0 failed** |
| `pmm_spec.spl` | 22 total, 16 passed, 6 failed | **22 total, 22 passed, 0 failed** |
| `vmm_copyin_spec.spl` | 16 total, 15 passed, 1 failed | **16 total, 15 passed, 1 failed (unchanged)** |

Bonus (not required by scope, but a direct consequence of fixing
`vmm_teardown_user_space`'s call sites): `test/01_unit/os/kernel/ipc/execve_spec.spl`
went from 3/8 to 4/8 passing — specifically its `vmm_teardown_user_space`
describe block (2 examples) flipped from failing to passing. Its remaining
4 failures are pre-existing, unrelated exec/ELF-dispatch issues, untouched.

### 5. Sabotage check

Reverted `vma_add`'s success branch to return `VmaAddResult(code: 0, space:
space)` (the original unmutated `space` instead of `updated`) and re-ran
`vmm_vma_spec.spl`: result went back to **18 total, 7 passed, 11 failed** —
the exact original baseline failure count. Fix restored and re-verified green
(18/18) immediately after. This proves the spec now genuinely exercises the
product's value-semantics behavior rather than passing vacuously.

### 6. Newly-surfaced failures triaged

No NEW genuine product failures surfaced in the 4 target specs — all 60
examples across the 3 previously-broken files now pass. The one remaining
failure (`vmm_copyin_spec.spl`, "copies a byte range that crosses two mapped
readable pages", `array index out of bounds: index is 0 but length is 0`) is
**pre-existing** (present, identical, before this fix), does not involve
`ProcessVmSpace` mutation (the function under test,
`vmm_copyin_bytes_from_space`, only *reads* the VMA list), and is unrelated
to this bug's root cause. Filed as a separate, un-investigated finding rather
than chased here — bounded effort per task scope.

### 7. Deliberately NOT fixed (documented, not chased)

`vmm_mmap` (`vmm_vma.spl`) has the **identical** defect one layer up: after
calling the now-fixed `vma_add`, it only returns `chosen as i64` (the mmap'd
address) — the updated `ProcessVmSpace` from `add_result.space` is still
never returned to `vmm_mmap`'s own callers
(`src/os/kernel/ipc/syscall_spm.spl` ×3, `src/os/kernel/loader/elf64.spl`
×1). This is now recorded inline in `vmm_vma.spl` at the `vmm_mmap` call
site. It was **not** fixed here because: (a) no spec anywhere in the repo
exercises `vmm_mmap` (grep-confirmed zero test call sites), so there is no
verification harness to prove correctness or catch a regression; (b) fixing
it would cascade into ≥4 more production call sites in files this task's
scope did not authorize touching, each needing its own further upward
threading; and (c) this matches the task's explicit bounded-effort
instruction to document rather than chase a larger, separate defect. This is
a real, live gap and should be scoped as its own follow-up.

---

## Symptom

```bash
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
    test/01_unit/os/kernel/memory
```

| spec | result | representative failure |
|---|---|---|
| `vmm_vma_spec.spl` | 18 total, 7 passed, **11 failed** | `adds single VMA — count becomes 1`: `expected 0 to equal 1` |
| `vmm_cow_spec.spl` | 18 total, 5 passed, **13 failed** | `semantic: array index out of bounds: index is 0 but length is 0` |
| `pmm_spec.spl` | 22 total, 16 passed, **6 failed** | `method total_memory not found on type _TestPhysMemManager` |
| `vmm_copyin_spec.spl` | 16 total, 15 passed, **1 failed** | `array index out of bounds: index is 0 but length is 0` |

The `array index out of bounds: index is 0 but length is 0` failures are a
*downstream* symptom, not the cause: the add never persisted, so the list is
empty and the later `[0]` read fails.

## Root cause

### 1. The specs never import the code they claim to test (shim vacuity)

`vmm_vma_spec.spl:72` defines its own copy, with the duplication stated
outright in its own docstring:

```
fn _space_add(space: ProcessVmSpace, area: VmArea) -> i32:
    """Local vma_add implementation for tests — same logic as vmm.spl."""
```

Counts of spec-local `fn _*` helpers vs. imports of the product module:

| spec | local `fn _` helpers | `use os.kernel.memory…` imports |
|---|---|---|
| `vmm_cow_spec.spl` | 8 | **0** |
| `vmm_vma_spec.spl` | 6 | **0** |
| `pmm_spec.spl` | 1 | **0** |
| `vmm_copyin_spec.spl` | 2 | 1 |

Three of the four import nothing from `os.kernel.memory`. `pmm_spec`'s
failures name `_TestPhysMemManager` — a type declared inside the spec — which
confirms the same pattern. So the real `vma_add`
(`src/os/kernel/memory/vmm_vma.spl:64`) is never executed by this suite.

### 2. Both the shim and the product mutate a by-value `struct` parameter

`ProcessVmSpace` is declared `struct` at
`src/os/kernel/types/vmspace_types.spl:45`. `struct` is a **value type**:
mutations to a parameter do not propagate to the caller. Proved with a minimal
probe (interpreter *and* JIT agree):

```
struct Space:
    areas: [i64]
    count: u64

fn add(s: Space, v: i64) -> i32:
    s.areas.push(v)
    s.count = s.count + 1
    0

fn main():
    var sp = Space(areas: [], count: 0)
    val rc = add(sp, 42)
    print "rc={rc} count={sp.count} len={sp.areas.len()}"
```

Output: `rc=0 count=0 len=0` — exactly the spec's
`expect(rc).to_equal(0)` passing while `expect(space.vma_count).to_equal(1)`
fails with `expected 0 to equal 1`.

Both `_space_add` (spec) and `vma_add`
(`src/os/kernel/memory/vmm_vma.spl:81-83`) end with

```
space.areas.push(area)
space.vma_count = space.vma_count + 1
0
```

i.e. they are written as if `ProcessVmSpace` were a reference type. **The
product function has the same defect as the shim** — it is a no-op for the
caller — it just is not what the suite measured.

Note: `.push()` itself is *not* the problem. It mutates in place in both
engines (probed separately: discarding vs. reassigning the result both give
`len=1`). Only the by-value struct parameter loses the write.

## Why not fixed now

The obvious one-line fix — change `struct ProcessVmSpace` to `class` so
mutation propagates — is **wrong and dangerous**. Fork/COW deliberately relies
on value-copy semantics: `vmm_vma.spl:404` does `child.areas.push(cloned)`
while building a child address space, and `vmm_copy.spl` copies spaces for
fork. Making the type a reference would silently alias parent and child
address spaces — a far worse kernel bug than the one being fixed, and exactly
what `vmm_cow_spec` exists to guard.

The correct fix is to make the mutating operations return the updated space,
which is already the established style in the same file — `vma_remove`
(`vmm_vma.spl:96`) is declared `-> ProcessVmSpace`. So `vma_add` should return
the new space rather than an errno-only `i32`, and the ~39 files that reference
`ProcessVmSpace` need their call sites checked.

That is a kernel-wide signature change across 39 files, in `vmm_*`/fork/COW
code, while other sessions are live in this tree — not something to land as a
drive-by test fix. And it must be paired with deleting the spec-local shims so
the suite actually exercises the product; otherwise the specs stay vacuous
whatever the product does.

**Recommended sequencing:**
1. Change `vma_add` (and any sibling mutator) to return `ProcessVmSpace`,
   updating call sites.
2. Delete `_space_add`, `_vma_overlaps_local`, `_TestPhysMemManager` and the
   other spec-local reimplementations; import the real symbols instead.
3. Re-run — the suite will then be measuring the product for the first time,
   so expect new, genuine failures to surface.

## Measurement note

`bin/simple test` runs specs on the **interpreter** and `bin/simple` here is
the Rust bootstrap seed (57MB, built 2026-08-04, prints the seed banner).

`--no-cache` and `--no-cover-check` are mandatory: without them a directory
holding 100+ specs can report `No test files found … Results: 0 total` and
**exit 0** (concurrent runs rewrite a shared path-scoped manifest), and a
missing `@cover` annotation aborts the run so zero specs execute. Both read
as "clean". Directory runs must also be sequential
(`.claude/rules/testing.md` F2). Treat any `0 total` result as **unmeasured**,
not passing — the counts above were all taken with both flags set.

## Follow-up 2026-08-10 — the fix landed on only ONE of the two duplicate test trees

`test/01_unit/` and `test/unit/` are duplicate trees and **both execute**. The
2026-08-04 fix was applied to `test/01_unit/os/kernel/memory/vmm_vma_spec.spl`
only; `test/unit/os/kernel/memory/vmm_vma_spec.spl` still carried the original
vacuous shims (`_space_add`/`_vma_overlaps_local`/`_space_find`, lines 68-98)
and was therefore still both re-implementing the code under test and relying on
by-value `ProcessVmSpace` mutation.

Vacuity re-proved by execution (interpreter, the engine `bin/simple test` uses),
running the stale `_space_add` shim standalone:

```
rc1(expect 0)         = 0
rc2(spec asserts -17) = 0      <-- EEXIST never fires
vma_count after 2 adds (spec asserts 1) = 0
areas.len()           = 0
```

`space.areas.push(...)` and `space.vma_count = ...` mutate a discarded copy, so
the second add sees an empty list and cannot detect the overlap. The
`expect(rc2).to_equal(-17)` assertion in the stale leg could never have been
testing overlap rejection.

The `test/unit` leg is now synced to the product-calling version. Verdicts:

| leg | before | after |
|-----|--------|-------|
| `test/unit/.../vmm_vma_spec.spl` | exit 1 (stale shims) | **18 total, 18 passed, 0 failed** |

Oracle liveness confirmed by sabotage: flipping `expect(r2.code).to_equal(-17)`
to `-18` gives `expected -17 to equal -18`, `18 total, 17 passed, 1 failed`,
exit 1 — the real `vma_add` (`src/os/kernel/memory/vmm_vma.spl:98`) genuinely
returns -EEXIST. **The allocator itself is correct**; only the spec was vacuous.

`vmm_cow_spec.spl` was checked: both legs are byte-identical and both already
carry the `_SimCowResult` fix. No other os/kernel memory spec has a by-value
struct-param mutation helper.
