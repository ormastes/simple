# `bin/simple test` never leaves `[setup] discover: begin` on large targets — two O(n^2) steps in the manifest reindex

**Date:** 2026-08-18
**Status:** ROOT-CAUSED and FIXED in pure Simple (`src/lib`, no bootstrap needed), with before/after measured on the real function over the real tree.
**Severity:** HIGH — the whole-suite command (`bin/simple test`, target `test/`) is unusable.

## Symptom

`bin/simple test` (target `test/`) prints

```
  [setup] discover: begin (target: test/)
```

and never prints the matching `[setup] discover: Nms (N file(s))` line. Killed at
1923 s with ~101 % CPU sustained throughout — **spinning, not blocked on I/O and
not deadlocked**. Two earlier whole-tree attempts died the same way (one at 920 s
to `scripts/resource/kill_simple_monitor.shs`). `test/01_unit` (8,223 spec files)
behaves identically.

Smaller targets complete: `test/01_unit/std` (934 spec files), `test/01_unit/lib`
(2,804), `test/02_integration` (760), `test/shared` (21) all reach a real
`Results:` line. `test/01_unit/lib` produced 33,888 *examples* without trouble, so
the cost is **not** example count — it is the number of indexed spec FILES.

## Verdict: superlinear cost, NOT a hang

The code terminates; it is quadratic in the number of indexed test files, twice
over. Evidence below.

### Measurement 1 — isolated micro-benchmark of the lookup

Probe builds a synthetic `TestManifest` of N entries and performs N lookups, once
via the shipped `manifest_find_entry()` and once via a path->index dict.
(`/mnt/data/tmp/disc/probe.spl` and `probe2.spl`, not committed — they only call
library functions.)

| N entries | `manifest_find_entry` x N | dict index x N | ratio |
|---|---|---|---|
| 250   | 23 ms    | 5 ms   | 4.6x |
| 500   | 55 ms    | 14 ms  | 3.9x |
| 1000  | 526 ms   | 34 ms  | 15x |
| 2000  | 1 732 ms | 95 ms  | 18x |
| 4000  | 8 935 ms | 233 ms | 38x |
| 8000  | 19 518 ms| —      | — |

Doubling N multiplies linear-scan time by 3.1x-5.3x (quadratic, drifting
super-quadratic under allocation pressure); the dict version scales linearly
(2.4x-2.8x per doubling). The same probe shows array `push` is linear and cheap
(8,000 pushes in 43 ms), which rules push out as the cause of the lookup curve.

### Measurement 2 — the real function on the real tree

`manifest_incremental_update(old, [dir])` with `old` = a 20,552-entry manifest of
every `*_spec.spl` under `test/`, one process, one binary
(`/mnt/data/tmp/classfix/release/simple`), same tree. The target `test/shared`
walks only **21** files, so anything slow here is proportional to `old`, not to
the walk:

| variant | `test/shared` (21 walked files, old = 20 552) |
|---|---|
| shipped code | **88 590 ms** |
| + dict index for the lookup only | **71 832 ms** (walk itself 96 ms; index build 88 ms) |
| + local-array accumulation (both fixes) | **3 316 ms** — **26.7x faster than shipped** |

The gated probe log pins the split exactly. With the dict index alone, the
**walk+reindex phase costs 96 ms** while the *carry-over* loop that follows
accounts for the remaining ~71.7 s — two independent quadratic terms, not one.
With both fixes the carry-over drops to ~3.1 s and stops dominating.

### Measurement 3 — after both fixes, full curve (`SIMPLE_TEST_DISCOVERY_DEBUG=1`)

Same 20,552-entry `old` manifest for every row, so the carry-over cost is
constant by construction and the walk cost is the variable under test:

| target | walked spec files | index build | walk+reindex | carry-over | **total** |
|---|---|---|---|---|---|
| `test/shared`      | 21    | 78 ms  | 84 ms    | 3 118 ms | **3 316 ms** |
| `test/02_integration` | 783   | 94 ms  | 403 ms   | 3 599 ms | **4 135 ms** |
| `test/01_unit/std` | 937   | 116 ms | 620 ms   | 3 297 ms | **4 036 ms** |
| `test/01_unit/lib` | 2 815 | 119 ms | 984 ms   | 3 605 ms | **4 719 ms** |
| `test/01_unit`     | 8 279 | 91 ms  | 2 656 ms | 2 589 ms | **5 361 ms** |

The walk term is now **linear** in walked files (21 -> 8 279 files, a 394x
increase, costs 84 ms -> 2 656 ms, a 32x increase — sublinear here because fixed
per-call overhead dominates the small end). Index build and carry-over are flat,
as they must be for a constant `old`. Extrapolating the walk term to the whole
`test/` tree (20 552 files) gives roughly 6-7 s of walk plus ~3 s of carry-over.

`test/01_unit` is the decisive row: **that target previously never cleared
`[setup] discover: begin` at all** (parent lane, and again in this session). It
now reindexes in **5.4 s**.

## Root cause

Both live in `src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl`,
`manifest_incremental_update()`, reached from the ordinary discovery path
*before* the `discover:` timing line is printed — `discover_test_files_fast` ->
`save_manifest_from_discovery` -> `manifest_incremental_update`
(`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:247`, `:373`). That is
exactly why the log freezes on `discover: begin`.

### (a) Linear scan per walked file — O(walked_files x old_entries)

```
                val old_entry = manifest_find_entry(old, f)
```

`manifest_find_entry` (`src/lib/nogc_sync_mut/test_runner/test_manifest.spl:302`)
is a full linear scan:

```
fn manifest_find_entry(manifest: TestManifest, path: text) -> TestManifestEntry:
    for entry in manifest.entries:
        if entry.path == path:
            return entry
```

The sdoctest half did the same via `manifest_find_sdoctest_entry`. For `test/`
that is ~4.2 x 10^8 text comparisons.

The function had already built the right data structure and **never read it**:
`old_paths` / `old_sd_paths` (`{text: bool}`) were populated and then dead. The
index existed; only the lookup still went the long way round.

### (b) Appending into a struct-field array — O(old_entries^2)

```
    for entry in old.entries:
        if not path_under_any(entry.path, dirs):
            manifest.entries.push(entry)
```

Reading the same 20,552-element array costs 88 ms (measured: the index-build
loop). Reading it *and appending each survivor to `manifest.entries`* costs
~71.7 s — ~800x more for the same iteration count. `manifest.entries.push(...)`
on this path is a read-modify-write of the whole field array: this module drops
off the JIT (`[jit-fallback] unresolved external symbol 'char_code': whole module
dropped to the interpreter`), and on the interpreter a struct-field append copies
the array. The identical pattern was present in the walk loop and in
`manifest_full_scan`.

Note this term is proportional to `old.entries` **alone** — it makes even a
21-file target take 70+ s once the index covers the whole tree, which is why the
defect looks like it appears out of nowhere.

## Why it looks intermittent

It only bites when a manifest **already exists**. A first-ever run on an empty
`.simple/test-manifest.idx` takes `manifest_full_scan` and looks fine.

## Where the fix belongs

**Pure Simple, `src/lib/**` — no bootstrap, no seed change.** The stdlib is read
as source on every process start (`.claude/rules/commands.md`), so the edit is
live immediately. Nothing in `src/compiler_rust/` is required.

(The *underlying* interpreter behaviour in (b) — struct-field append being O(n) —
is seed-resident and is NOT fixed here; it is worked around in this module. It
deserves its own record.)

## Fix (landed)

`src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl`:

1. `manifest_incremental_update` builds a `{text: i64}` path->index map once
   (replacing the dead `old_paths` / `old_sd_paths` sets) and resolves each walked
   file with `contains_key` + a direct array index. Semantics unchanged: identical
   reuse condition on `file_size` + `file_mtime`, identical fallback to
   `scan_test_file`.
2. `manifest_incremental_update` and `manifest_full_scan` accumulate into **local**
   arrays and assign `manifest.entries` / `manifest.sdoctest_entries` once at the
   end, instead of appending into the struct field inside the loop.
3. Level-gated probe logs (`SIMPLE_TEST_DISCOVERY_DEBUG=1`, default off, per
   `.claude/rules/code-style.md`) report the index build, the walk+reindex phase
   and the carry-over phase separately, so the next operator can tell "slow" from
   "dead" without re-deriving any of this. These are retained deliberately.

## Verification status

* **Proven:** the two quadratic terms, and their removal, by the three
  measurement tables above — all taken in ONE tree with ONE binary
  (`/mnt/data/tmp/classfix/release/simple`), toggling only the code under test.
* **Proven:** `manifest_incremental_update` over the real 20,552-entry index goes
  from 88 590 ms to 3 316 ms for `test/shared`, and `test/01_unit` — a target that
  previously never completed — now finishes in 5 361 ms.
* **Not re-measured:** a full `bin/simple test test/ --list` end to end. The shared
  box carried 20-96 concurrent `simple` processes from other lanes throughout this
  session and process startup alone exceeded three hours on repeated attempts, so
  no whole-tree runner invocation completed inside the session. Per
  `.claude/rules/testing.md` a run with no `Results:` line is INCONCLUSIVE and is
  not claimed here. The numbers above are for the reindex step itself, which is
  precisely the step that was frozen.

## Adjacent, not fixed here

* `discover_test_files_slow` reads the full content of every candidate file
  (`read_file_content` per file): O(n) with a large constant, and the dominant
  remaining cost on `test/`.
* `rt_file_stat` appears to return the file SIZE, not an mtime — every manifest
  row in `.simple/test-manifest.idx` has `size == mtime` (e.g.
  `...if_else_implicit_return_spec.spl|5956|5956|...`). Change detection is
  therefore size-only: a same-size edit is not noticed. Separate defect.
* `[jit-fallback] unresolved external symbol 'char_code'` drops this whole module
  to the interpreter ("expect ~100-1000x slowdown", the runtime's own words),
  which is what turns both quadratic terms from annoying into fatal.
