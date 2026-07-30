# native-build --entry-closure: O(n²) line scan deterministically hangs (compute spin)

**Status:** FIXED 2026-07-12, corrected 2026-07-13 — `_nb_line_end` and
char-by-char `substring` scans use native single-pass `split("\n")` and
`index_of()` operations.
**Severity:** Blocking — any `native-build --entry-closure` invocation with a
multi-directory `--source` set (e.g. `--source src/compiler --source src/app
--source src/lib`) spins at ~100% CPU on one thread and never produces output.
**Affected file:** `src/app/io/_CliCompile/compile_targets.spl`
(`_native_build_entry_closure`, `_nb_line_end`, `_nb_module_path_from_use`).
**Introduced by:** commit `99f441126e0` ("fix(native-build): scan entry
closure without split arrays", 2026-07-11), which replaced a
`content.split("\n")` for-loop with a manual char-by-char scan.
**Path:** `bug` track.

## Symptom

Running (from a worktree, via the Rust bootstrap seed):

```bash
rm -rf build/bootstrap/native_cache
<seed> run src/app/cli/native_build_main.spl -- \
  --backend cranelift --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 16 --cache-dir build/bootstrap/native_cache \
  --mode dynload --entry src/app/cli/main.spl \
  --runtime-path <repo>/src/compiler_rust/target/bootstrap -o <out>
```

hangs deterministically: 100% CPU on one thread, log output frozen at
byte-identical offsets (41896B non-LLVM seed / 46642B with `stdbuf -oL`
line-buffering) across repeated runs and across two different seed builds
(55MB and 144MB). No further output, ever (observed for 10+ minutes; a
standalone repro of the hot function alone stalled at file #349/~407 queued
after several minutes without completing).

## Root cause

The visible log content (deprecation/export-use lint warnings, then five
`[gc-warning]` higher-layer-import lines) is emitted by the **seed's own
module-load lint pass** while it parses `native_build_main.spl`'s transitive
`use` chain (i.e. the compiler's own support modules) — this all happens
*before* `cli_native_build`'s body starts running. The BFS import-closure walk
(`_native_build_entry_closure`, gated behind `--entry-closure`) then runs
silently afterward (it only prints when `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`
is set), which is why the log appears frozen with no indication of where the
spin actually is.

`_native_build_entry_closure` calls `_nb_line_end(content, pos)` once per
character position to find the next `"\n"`:

```simple
fn _nb_line_end(content: text, start: i64) -> i64:
    var pos = start
    while pos < content.len() and content.substring(pos, pos + 1) != "\n":
        pos = pos + 1
    pos
```

The interpreter's `substring`/`slice` builtin
(`src/compiler_rust/compiler/src/interpreter_method/string.rs:276-296`)
always rebuilds a `Vec<char>` of the **entire** receiver string per call
(`s.chars().collect()`) unless the requested range is the whole string
(`start == 0 && end >= s.len()`). A single-character `substring(pos, pos+1)`
call therefore costs O(content length), and `_nb_line_end` makes that call
once per character — turning an intended O(n) line scan into **O(n²) per
file** (confirmed live via `gdb` on the hung process: repeated
`core::str::iter::Chars::next`/`Vec::extend_desugared` frames inside the
`substring` builtin, and `HashMap::get` via
`interpreter_call::is_current_module_candidate` from the surrounding
interpreted method-call dispatch — both are generic "interpreter busy running
interpreted Simple" evidence, not spin-site evidence by themselves; the
decisive evidence was tracing `_native_build_entry_closure` directly, see
Verification below).

`_nb_module_path_from_use`'s inner delimiter scan had the identical
char-by-char `rest.substring(ri, ri + 1)` pattern, bounded by single import
line length so far less severe, but the same anti-pattern.

For a repo with ~500 files in the transitive closure of `src/app/cli/main.spl`
(and many more candidates across the 3 `--source` roots), individual larger
compiler source files (tens of KB) each cost tens of millions to billions of
character-copy operations just to find line breaks — deterministically
"hangs" for all practical purposes even though the loop technically
terminates.

## Verification

**Before fix** — isolated the BFS with `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`:
the `[native-build] closure visited N ...` trace lines crawl (visibly
slowing down on larger files) and the process never completes.

**After fix** — standalone probe (patched `_native_build_entry_closure` +
helpers extracted verbatim, called directly):

```
TOTAL 498 elapsed_ms=2199
```

(Previously: never reached completion; a prior isolated run stalled at
file #349/queued=407 without finishing after several minutes.)

Full build command, with `SIMPLE_COMPILER_PHASE_PROFILE=1`:

```
[BOOTSTRAP-PHASE] +1ms phase1:load_sources:start
[BOOTSTRAP-PHASE] +456ms phase1:load_sources:done n_sources=493
[BOOTSTRAP-PHASE] +456ms phase2:parse:start
[BOOTSTRAP-PHASE] +457ms phase2:parse:file:start src/app/cli/main.spl chars=773
error: semantic: type mismatch: cannot convert array to int
```

The entry-closure BFS + source loading (previously an infinite/near-infinite
spin) now completes in **456ms**. The build then fails fast with a distinct,
pre-existing error inside the interpreted `parse_full_frontend` call on the
tiny (773-char) entry file — unrelated to this fix (this code path was never
reachable before because the closure BFS always hung first; native-build was
already documented at 0/15 passing at baseline behind a different wall, see
commit `60d2474620327551297c1412fbf361ecd0da0db3`). That "array to int" parse
error is a **separate, out-of-scope** blocker; not investigated further here.

## Fix

- `_nb_line_end` deleted; `_native_build_entry_closure`'s per-file scan now
  uses `for raw in content.split("\n"):`. This remains a single native O(n)
  pass and is available in the pure-Simple compiler runtime. The initial
  `split_lines()` spelling crashed deployed Stage 4 with `Function
  'str.split_lines' not found`; that separate surface gap is tracked in
  `pure_simple_text_split_lines_missing_2026-07-13.md`.
- `_nb_module_path_from_use`'s delimiter scan now uses
  `rest.index_of(delim)` per candidate delimiter (5 native O(n) scans)

## 2026-07-17 compiled-Dict hardening

The full CLI helper had regressed to local `Dict<text, bool>` and
`Dict<text, text>` values for its discovered set and resolution cache. Compiled
local Dict mutation is not a reliable bootstrap primitive and is also the wrong
hot-path ownership for a hundreds-of-modules closure walk.

The discovered set now reuses the compiler driver's proven 8,192-bucket exact
text set. The resolution cache uses the same array-backed bucket representation
with tab-delimited key/value entries, including a presence bit so cached empty
resolution results remain distinguishable from misses. Every mutation is
explicitly reassigned.

A current pure-Simple compiler drove the modified module through parsing,
lowering, and into parallel object emission. The isolated compile then exhausted
the host's remaining disk space while writing unrelated compiler objects; no
source diagnostic was emitted, and no retry was made. The source contract now
rejects reintroducing either local Dict declaration. This hardens the future
full-CLI `native-build --entry-closure` path; the exact Stage4 bootstrap entry
uses the separate compiler-driver closure and is not claimed fixed by this
change.
  instead of a char-by-char loop.
- `test/01_unit/app/cli_native_build_main_contract_spec.spl` updated to
  assert the new implementation (and the absence of the old O(n²) patterns)
  instead of the old (buggy) structure it previously locked in.

## 2026-07-25 shared scanner follow-up

The CLI closure walker still split every source into lines and maintained a
second import parser. Besides retaining whole-file allocation on the hot path,
that parser treated `use` text inside docstrings as a real dependency.

Use/import/export-use discovery now delegates to the compiler driver's shared
byte scanner. A guarded sibling scanner retains `mod` and
`export member.*` compatibility while skipping comments and docstrings. The
CLI's duplicate `_nb_module_path_from_use` parser and unconditional line split
are removed. Focused scanner assertions cover real and fake sibling
declarations, and the CLI source contract pins delegation.

The deployed pure-Simple tool segfaulted before the focused tests, optimizer,
or source check could report results. No seed substitution or retry was made;
the earlier 456 ms receipt remains historical evidence, not performance credit
for this follow-up.

## 2026-07-26 interpreted shared-scanner repair

The shared byte scanner regressed the seed-interpreted native-build worker:
after 180 seconds it had visited only 25 files. The existing text scanner uses
native `split` and `find` operations and preserves the same comment, docstring,
lazy-import, and token rules, so the byte loop and its compatibility fallback
were collapsed to that implementation.

With the same source roots, entry, cache, backend, and 180-second cap, closure
discovery completed all 404 files and entered `CompilerDriver`; at 71 seconds
it had visited 175 files, versus 25 in the baseline run. The focused behavioral
and source gate passes 4/4. The bounded run ended in the driver phase, so the
source-matched compiler and downstream `73`/`84` gates remain open.

The final allowed incremental cycle confirmed the next boundary: phase-one
loading completed 402 unique sources in 6.9 seconds, but seed-interpreted
parsing took 179 seconds for the 25 KB entry and remained on the 67 KB driver
module when the ten-minute cap expired. Closure discovery is no longer the
build blocker; parser performance is. No fourth build cycle was started.

## 2026-07-30 current self-hosted host-WM regression

A clean current-main host-WM build reused a 317-object cache and invoked the
release pure-Simple compiler with Cranelift, entry closure, eight threads, and
stub fallback disabled. After 15 minutes the native-build log was still empty,
the cache still contained exactly 317 objects, and no output binary existed.
The process remained CPU-active until the bounded attempt was terminated
cleanly with exit 143.

A one-second process sample placed all 822 samples below
`CompilerDriver.parse_all_impl`, through `parse_full_frontend`,
`parse_module_body`, `parse_fn_decl`, and expression parsing. This is not the
fixed closure-scanner defect above and not 2D runtime compilation: current
self-hosted parsing failed to reach object-cache or link work. The same
317-module WM target completed in 22.5 seconds on 2026-07-27, so this is a
concrete parser/front-end performance regression. No bootstrap, seed fallback,
source workaround, or retry was used.
