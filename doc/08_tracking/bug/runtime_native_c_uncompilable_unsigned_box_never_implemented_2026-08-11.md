# `src/runtime/runtime_native.c` does not compile at origin/main — unsigned heap box referenced but never implemented

- **Status:** **RESOLVED 2026-08-11** — unsigned heap box implemented; `clang` 33 errors → **0**;
  `native-build` exit 1 → **0** and the produced binary prints `hello`. See "Resolution" at the bottom.
  A sixth pre-push guard (`scripts/check/check-c-runtime-compiles.shs`) now closes the guard gap.
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

---

## Resolution (2026-08-11)

### The ABI was never a guess — it was already pinned by the pure-Simple twin

The prior triage declined to implement because items 1-5 looked like a free ABI choice on
the same seam the stage3 SIGSEGV implicates. That reading was wrong in one decisive way:
**`src/runtime/simple_core/core_values.spl` is the pure-Simple twin of these exact symbols
and already implements the box.** Per `THREE implementations not two` (seed / pure-Simple /
runtime C), the C side had to be made to agree with it, not to invent a shape.

`core_values.spl:29-41`:

```
pub fn rt_value_u64(bits: i64) -> i64:
    val ptr = calloc(1, 16)
    spl_store_i64(ptr, 0, 0x55494E54)
    spl_store_i64(ptr, 8, bits)
    return ptr | 1
```

Every field of the C box is therefore **derived, not chosen**:

| item | derivation | source |
|------|-----------|--------|
| magic `RT_VALUE_HEAP_UINT = 0x55494E54U` (`"UINT"`) | stored at offset 0 by the twin and read back masked to 32 bits at **7** further sites (`core_values.spl:25,40`, `core_bdd.spl:39`, `core_array_query.spl:38`, `core_string.spl:507,518,519`) | twin |
| 16-byte size, kind@0 (32-bit), scope@4, payload@8 | `calloc(1, 16)`, `store_i64(ptr,0)` read as `& 0xFFFFFFFF`, `store_i64(ptr,8)` | twin |
| zeroed `transient_scope_id` | `calloc` zeroing; matches `rt_value_int_wide`'s explicit `n->transient_scope_id = 0` | twin + `RtCoreWideInt` |
| tag `\| RT_VALUE_TAG_HEAP` | `ptr \| 1` | twin |
| `uint64_t` payload | consumers compare `u->value == (uint64_t)expected`, `u->value <= (uint64_t)(INT64_MAX >> 3)` | call sites 3202/3287-3328/7662 |
| allocator, registry, OOM fallback | copied structurally from `rt_value_int_wide` | same file |
| accessor guard order | copied from `rt_core_as_heap_int`: tag test → null test → **registry membership** → `->kind`, so a stray TAG_HEAP-aliasing i64 is never dereferenced | same file |

Note the magic deliberately **breaks** the `STR1`/`FLT1`/`INT1` "…1" suffix pattern. Guessing
`"UNT1"` from the C file alone would have compiled, passed every existing guard, and silently
disagreed with the twin — precisely the silent corruption the prior triage feared. The layout
was verified byte-for-byte against the twin's expectations (size 16, kind@0 little-endian low
half of the 8-byte load == `0x55494E54`, payload@8 round-trips `0xFFFF...FF`).

`rt_value_as_u64` was **also** missing (used at `runtime_native.c:6858`, hidden behind clang's
error limit — the true count is 33, not 20/63, measured with `-ferror-limit=0`).

### Changes

- `src/runtime/runtime_native.c` — `RT_VALUE_HEAP_UINT`, `RtCoreUInt`, `rt_core_as_heap_uint`,
  `rt_value_u64`, `rt_value_as_u64`, plus `RT_VALUE_HEAP_UINT` arms in the leaf-kind switches
  at `rt_core_registered_object_kind`, `rt_core_reclaim_transient_immortal` and
  `rt_core_transient_classify`. The fourth switch needed no change: classify already folds all
  leaf kinds to `RT_CORE_TRANSIENT_FLOAT`, which is correct by layout identity.
- `src/runtime/runtime.h` — public declarations for `rt_value_u64` / `rt_value_as_u64`.

### Verification

| check | before | after |
|-------|--------|-------|
| `clang -fsyntax-only -ferror-limit=0 -std=gnu11` on `runtime_native.c` | **33 errors** | **0** |
| all 43 standalone-compilable `src/runtime/*.c` | 1 failing | **0 failing** |
| real `-c -fPIC -O2 -std=gnu11` object build of the 14 lane sources | — | **14/14 objects, 0 failures** |
| `bin/simple native-build hello.spl` | exit **1** | exit **0** |
| `./build/native/hello` | — | prints `hello`, exit **0** |

`nm` confirms both symbols exported from `runtime_native.o` (`T rt_value_u64`, `T rt_value_as_u64`).

### Guard gap closed

`scripts/check/check-c-runtime-compiles.shs` — sixth mandatory pre-push guard. Syntax-checks
every `src/runtime/*.c` with the real lane's flags (`-std=gnu11 -I src/runtime -I
src/runtime/platform`, from `runtime_compiler.spl`). Same verdict convention as the other five
(`PASS -- <n> file(s) checked` / `FAIL` exit 1 / `ERROR -- nothing was checked` exit 2; a run
that checks 0 files is an ERROR), fail-closed on cwd, with a fatal 5-fixture `--selftest`.

Two files are rostered as skipped — `counterpart_worker_runtime` (needs vendored
`simple_counterpart_abi.h`) and `scv_wasm_shim` (needs `wasmtime.h`). The skip cannot fail
open: it applies **only** when the failure is a single missing-external-header fatal, so a
genuine syntax error in those same files still FAILs (selftest fixture 4 locks this).

Proven fail-closed on the real defect: renaming the `RtCoreUInt` typedef made the guard report
`FAIL -- 1 of 43 file(s) failed to compile: runtime_native` (exit 1); reverting restored
`PASS -- 43 file(s) checked, 0 errors` (exit 0) with the blob hash byte-identical before and
after (`7e7035be10ffdb23eca0ec25038aaad3ebde3434`), i.e. zero residue.

One guard bug was found and fixed during that proof: the first cut keyed on stderr emptiness
rather than compiler exit status and so reported FAIL on `src/runtime/runtime.c`, which only
warns. Selftest fixture 2b now locks the regression.

### Still open (unchanged by this fix)

`bootstrap/stage3/simple native-build` still exits **139** — the separate tagged-value
field-index collision in
`stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`. What changes is
that the seed lane now works, so an unstripped stage3 can be produced and that SIGSEGV can
finally be diagnosed.
