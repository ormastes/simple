# Stage4 deep-free chain — status, blocker, and next steps (2026-07-25)

**Goal:** stop Stage4's ~111GB peak, which blocks redeploy, which blocks the
RISC-V FPGA goal (AC-1..AC-12, all still unmet).

**Root cause (established earlier, unchanged):** `evict_sources()` /
`evict_ast()` / `evict_hir()` in `src/compiler/80.driver/driver_types.spl`
rebuild and reassign their containers but never free anything. On this no-GC,
no-refcount runtime, dropping a reference reclaims NOTHING. Measured:
filling 5,000 strings registered **+10,002** heap objects; applying the evict
pattern reclaimed **0**.

## State: 3 of 5 steps landed. NOT verified end to end. 111GB UNCHANGED.

| # | step | state | commit |
|---|------|-------|--------|
| 1 | C `rt_string_free` + tombstoned registry | LANDED, self-checked | `d55fe0c67d6` |
| 2 | Rust-runtime parity | LANDED, builds + `nm` confirms symbol | `9b97fa0c22b` |
| 3 | extern surface across backends + seed registries | LANDED | `d479d1a4302` |
| 3a | revert bad CORE_REQUIRED classification | LANDED | `34c40a95b28` |
| 4 | `evict_sources()` call site | **written, NOT committed** | — |
| 5 | reclamation measurement | **BLOCKED** | — |

Steps 1-3 are plumbing. **Nothing frees anything on the Stage4 path yet.**

### Why step 1 was needed at all
Strings register into `rt_core_immortal_registry`, an open-addressing table with
**no deletion** — hence "immortal". Erasing a slot by writing 0 truncates any
probe chain running through it, so unrelated LIVE strings silently read as
unregistered. Deletion now writes a tombstone (terminates insertion, not
lookup; counted against the load factor; dropped on rehash).

`rt_string_free` REFUSES rather than trusts: non-heap-string, absent from the
registry (already freed), or `RT_CORE_STRING_FLAG_SHARED` — the two
process-wide caches (`rt_core_short_string_cache` for len<=1,
`rt_literal_intern_table`), whose objects go to unrelated callers.
**A refusal leaks; a wrong free corrupts. The bias is deliberate.**

Validated by `src/runtime/test/rt_string_free_selfcheck.c`, 16 assertions, plus
a **negative control**: swapping the tombstone for a naive `= 0` erase fails
exactly the 3 probe-chain assertions, so the check is not vacuous.

### Why step 4 is safe where it runs (verified, not assumed)
- `bootstrap-from-scratch.sh:508` passes `--low-memory`;
  `bootstrap_api.spl:107` sets `options.low_memory = true`;
  `driver.spl:258` calls `evict_sources()` under it — **the call site is live in
  Stage4**, and dead in any normal build.
- `driver.spl:850` gates the HIR-reparse fallback on `(not options.low_memory)`,
  so the only post-phase-2 reader of `src.content` is disabled exactly when the
  free happens.
- Only `content` is freed. `rt_string_new` always memcpy's, so no lexer output
  can alias a file's own content buffer. `path` / `module_name` are NOT freed —
  they are carried into the replacement `SourceFile` and may alias arena slots.

## THE BLOCKER (open, unresolved)

`native-build` fails for the probe shape on the current seed:

```
error: AOT compile error in <module>: MIR module has no functions
error: native-build worker exited with code 1
```

Established by controlled comparison:
- The same probe file **built and ran clean on the OLD seed** (06:43 build).
- A **control probe that does not mention `rt_string_free` at all fails
  identically** — so this is not about the new symbol.
- **But a trivial `fn main(): print "hi"` builds and runs FINE (rc=0) on the
  current seed** — so native-build is NOT broken across the board. An earlier
  draft of this document said it was; that was wrong.
- The seed is also healthy for non-native lanes: `simple run` on a trivial
  file prints `ok`; the interpreter lane resolves `rt_string_free` with no
  dispatch error.

So the trigger is some feature the probes use and the trivial file does not.
The candidates, not yet discriminated at the time of writing, are a
module-level `extern fn` declaration and/or `fn main() -> i64` (a main with a
return type) under `--entry-closure`. Two single-variable probes
(`probes/freeprobe/varA.spl` = return type only, `varB.spl` = extern only) were
queued to separate these; **read their result before bisecting the seed**, since
a positive there localises the defect far faster.

**A first hypothesis was WRONG and is recorded to stop it being re-tried:**
marking `rt_string_free` as `CORE_REQUIRED_RUNTIME_SYMBOLS` really was a bug
(`runtime_archive_has_core_required_symbols` requires the freestanding
`simple_core` archive to define it, and it does not), and the revert
`34c40a95b28` is correct on the merits — **but removing it did NOT fix the
build.** That commit's message claims more than it delivered.

**Do NOT dismiss this signature as environmental.** Two earlier agent reports
called this exact `MIR module has no functions` an environmental quirk of a
stale worktree. It reproduces in the main repo on a fresh seed.

## Next steps, in order

1. **Bisect the seed.** Revert my remaining seed edits one at a time, rebuild,
   and retry the trivial native-build. Candidates, in likelihood order:
   `runtime_sffi.rs` (`RuntimeFuncSpec`), `elf_utils.rs`,
   `interpreter_extern/{mod,sffi_string}.rs`, `runtime/src/value/mod.rs`.
   Also rule out a working-copy `src/compiler/**` edit from a parallel session
   (`cuda_backend.spl`, `contracts.spl` were dirty), and the uncommitted
   `driver_types.spl` change itself.
2. Once native-build is green, run `probes/freeprobe/free_probe.spl`. It must
   report a **negative** `delta_free` and `freed=5000`. `freed=0` means the
   value is still being marshalled as a raw pointer, not a tagged value.
3. Only then commit `driver_types.spl` (step 4).
4. Then one bounded Stage4 run to measure the actual peak. Expect only a
   partial win: `content` is one allocation class among several, and
   `evict_ast()` / `evict_hir()` still free nothing.

## Landmines burned this session (each cost a cycle)

- **`--runtime-bundle core-c-bootstrap` stages the RUST archive**, not
  `runtime_native.c`. `cargo build -p simple-runtime` refreshes only
  `target/debug`; that lane links the **bootstrap** profile. Verify with
  `nm target/<profile>/libsimple_runtime.a | grep ' T <sym>'`.
- **Marshalling is per-SYMBOL, not per-type.** `extern fn f(x: text)` does not
  imply a tagged value: `rt_string_len(s: text)` is tagged `int64_t`,
  `rt_file_exists(path: text)` is a raw `const char*`. The mapping is
  `RuntimeFuncSpec` in `runtime_sffi.rs`; unregistered symbols default to the
  pointer form, so a probe silently refuses everything and still exits 0.
- **A new extern needs FIVE places** or it fails differently per lane:
  `RUNTIME_SYMBOL_NAMES`, `runtime_sffi.rs`, `elf_utils.rs`,
  `interpreter_extern/` dispatch, and the `value/mod.rs` re-export (missing the
  last one fails the Rust build outright). `CORE_REQUIRED` is NOT one of them.
- **`tail -N` on a build log hides the real error** — the useful line was 13
  lines in, under 350 lines of `gc-warning`. Keep a persistent `--cache-dir`
  and grep the whole log.
- **Self-matching `pgrep`/`pkill`**: a waiter whose heredoc contains
  `pgrep -f 'cargo build'` matches its own wrapper and waits forever;
  `pkill -f probe4.sh` from a tool call containing that string kills the call
  itself (exit 144). Both happened here. Use the harness's background
  completion notification instead of hand-rolled waiters.

## Known risk

`src/compiler/70.backend/sffi_minimal.spl` in the working copy declares
`rt_string_free` as **void**, while main has the `-> i64` fix. Backends key
their type tables by symbol NAME, so committing that working-copy version
re-introduces the signature conflict on main.
