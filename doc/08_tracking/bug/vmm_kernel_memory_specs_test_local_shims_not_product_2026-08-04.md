# BUG: `test/01_unit/os/kernel/memory/` specs test spec-local copies, not `src/os/kernel/memory/` — and both copies share a real value-semantics defect

**Status:** OPEN
**Found:** 2026-08-04
**Severity:** high — 31 failing examples, and the specs are **vacuous**: they
cannot observe the product module at all, so fixing `src/os/` would not turn
them green and a product regression would not turn them red.

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
