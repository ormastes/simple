# `src/runtime/runtime_native.c` does not compile at origin/main — unsigned heap box referenced but never implemented

- **Status:** OPEN — root-caused, not fixed (fix is feature work on a tagged-value ABI; see Why not fixed here)
- **Date:** 2026-08-11
- **Severity:** BLOCKER — this is the reason there is **no working native compile path on this host at all**.
- **Signal:** exit **1**, `clang` diagnostics. Not a segfault. Distinct from, and **upstream of**, the stage3 SIGSEGV filed in `stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`.

## Minimal repro

```bash
cd /home/ormastes/dev/pub/simple
printf 'fn main():\n    print("hello")\n' > /tmp/hello.spl
./bin/simple native-build /tmp/hello.spl ; echo $?        # 1
```

Take `$?` from the command directly — a pipe launders it.

Narrower, compiler-independent repro (no `bin/simple` involved):

```bash
cp -r src/runtime /tmp/rt && clang -fsyntax-only -I/tmp/rt /tmp/rt/runtime_native.c 2>&1 | grep -c error:
# 63 errors
```

## The defect

`runtime_native.c` contains **8 call sites** referencing an unsigned heap-box type and
accessor that are **declared nowhere in the repository**:

| line | expression |
|------|------------|
| 2191 | `return rt_value_u64(bits);` |
| 3202 | `RtCoreUInt* u = rt_core_as_heap_uint(value);` |
| 3287, 3288 | `RtCoreUInt* left_uint = rt_core_as_heap_uint(left);` (+ right) |
| 3327, 3328 | same pair, second comparison path |
| 7662, 7683 | `RtCoreUInt* u = rt_core_as_heap_uint(k);` (dict key canonicalisation) |

```
grep -rl 'RtCoreUInt'          src/  ->  src/runtime/runtime_native.c   (uses only)
grep -rl 'rt_core_as_heap_uint' src/  ->  src/runtime/runtime_native.c   (uses only)
grep -rn 'RT_VALUE_HEAP_UINT'   src/  ->  (no matches)
```

There is **no typedef, no accessor, no kind constant, no allocator, and no registry** for
this box. `rt_value_u64` likewise has no C declaration (only a same-named Simple function in
`src/runtime/simple_core/core_values.spl`, which does not declare it to C).

Consequences under C99: `rt_core_as_heap_uint` is an implicit declaration returning `int`,
so `RtCoreUInt* u = rt_core_as_heap_uint(v)` is an int-to-pointer conversion, and `u->value`
is a member access on an unknown type. 63 errors; `clang` stops at the error limit.

## This has never compiled

A scan of the last 40 commits touching the file finds the typedef in **none** of them:

```bash
for c in $(git log --format=%H -40 origin/main -- src/runtime/runtime_native.c); do
  git cat-file -p $c:src/runtime/runtime_native.c | grep -q '} RtCoreUInt;' && echo "PRESENT $c"
done   # -> no output
```

So this is **not a clobber or a half-landed merge** — the call sites were authored and landed
without their declarations ever existing. The unsigned-value-semantics campaign
(`7e327623f6c fix(runtime): preserve unsigned value semantics`, and the local-only duplicates
`f1842dc1029` / `5f3066c9ca3`) landed the *consumers* of an unsigned box and never landed the box.

**Guard gap:** nothing in the pre-push guard set compiles the C runtime, so a
non-compiling `src/runtime` reaches `main` green. This is the actionable process finding.

## What the intended design appears to be

An exact structural precedent already exists in the same file — the signed wide-int box:

```c
/* runtime_native.c:899 */
typedef struct RtCoreWideInt {
    uint32_t kind;              /* RT_VALUE_HEAP_INT (0x494E5431U, "1TNI") */
    uint32_t transient_scope_id;
    int64_t  value;
} RtCoreWideInt;
static inline RtCoreWideInt* rt_core_as_heap_int(int64_t value);   /* :1588 */
```

and the parallel `RtCoreFloat` / `RT_VALUE_HEAP_FLOAT` / `rt_core_as_heap_float` triple.
The call sites read `u->value` against a `uint64_t`, and site 2190-2191 shows the intent:

```c
if (value <= (uint64_t)(INT64_MAX >> 3)) return rt_value_int((int64_t)value);
return rt_value_u64(bits);              /* values that do NOT fit the signed path */
```

i.e. a **distinct unsigned box** for u64 values that overflow the signed/tagged range.

## Why this was not fixed here

Completing it is feature work on the tagged-value ABI, not a mechanical repair. A correct
implementation must add, coherently and atomically:

1. a `RT_VALUE_HEAP_UINT` magic constant that does not collide with `"FLT1"`/`"1TNI"`/`"1RTS"`;
2. the `RtCoreUInt` typedef with the shared leaf layout;
3. an allocator + immortal-registry registration (mirroring `rt_core_register_float`);
4. `rt_core_as_heap_uint` with the registry-membership-before-dereference guard;
5. new `case` arms in **every** lifecycle switch that enumerates leaf kinds —
   at minimum `runtime_native.c:954`, `:1525`, `:1854`, `:1937`;
6. `rt_value_u64`, plus signed/unsigned mixed-comparison semantics at sites 3287-3328.

Guessing any of items 1-5 risks a wrong layout on exactly the tagged-value seam that the
sibling stage3 SIGSEGV filing implicates. Per `.claude/rules/code-style.md` (no cover-up
fixes), this is filed rather than fabricated.

## Relationship to the stage3 SIGSEGV

Two independent blockers, both live:

| path | failure | cause |
|------|---------|-------|
| `bin/simple` (Rust seed) `native-build` | exit **1** | this bug — C runtime will not compile |
| `bootstrap/stage3/simple native-build` | exit **139** | `stage3_native_build_segv_..._2026-08-11.md` |

Fixing this one restores a working compile path via the seed, which is the prerequisite for
producing an unstripped stage3 and thereby diagnosing the SIGSEGV. **This bug should be fixed
first.**

## Correction to the sibling filing

The sibling filing recorded, as a hypothesis, that the crash correlated with 12 `UU`
unmerged files and a `<<<<<<< HEAD` marker at the top of `src/runtime/runtime.h`.
**That working-copy state is now resolved** (`git status` reports 0 `UU`; `runtime.h` starts
with a normal comment). Re-measured after resolution:

- `bootstrap/stage3/simple native-build` on both `\n` and hello world: **still exit 139**,
  same binary (`md5 2244f18ce2e694fb7ca395e9916404c3`, all three stages identical).
  The mid-merge state was therefore **not** the cause of the SIGSEGV; that hypothesis is refuted.
- The seed's failure *changed* from the conflict marker to the 63 errors documented above.

Additionally, the local working copy's `src/runtime` had diverged from origin via two
**local-only, superseded** commits (`f1842dc1029`, `5f3066c9ca3`) that truncated
`runtime.h` by 180 lines and left `runtime_native.c` including a
`runtime_terminal_signal_scope_impl.h` that exists in neither the worktree nor origin.
`src/runtime` was restored to `origin/main` (`git checkout origin/main -- src/runtime`),
a strictly forward move per `.claude/rules/vcs.md` (origin supersedes). Those two commits
remain in local history and nothing was lost. The 63 errors reproduce on that
byte-identical-to-origin tree, which is what establishes the defect is landed, not local.

## Unblock condition

Implement items 1-6 above, then:

```bash
clang -fsyntax-only -I src/runtime src/runtime/runtime_native.c   # must be 0 errors
./bin/simple native-build /tmp/hello.spl && /tmp/hello            # must print: hello
```

Then bootstrap an **unstripped** stage3 and re-measure the sibling SIGSEGV filing's table.

## Recommended guard

Add a pre-push / CI check that runs `clang -fsyntax-only` over `src/runtime/*.c`.
The existing five guards are all git-tree-shaped and cannot catch a non-compiling runtime.
