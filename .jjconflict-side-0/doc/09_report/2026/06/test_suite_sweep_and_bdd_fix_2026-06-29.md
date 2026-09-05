# Full-suite test sweep + fixes — 2026-06-29

## Update (later 2026-06-29): second systematic fix + decisive categorization

**Fix #2 landed — cross-module array write-back lost in BDD closures.** A
cross-module function that builds a `[u8]` via an in-place append helper returns
a TRUNCATED array only when called from a BDD it-block (correct from main).
Converted `encoding/{msgpack,bson,cbor}` append helpers to return-based +
reassign — all three specs now **0 failures** (commits `f81e3804`, bson/cbor
follow-up). Seed bug filed:
`doc/08_tracking/bug/interp_crossmodule_array_writeback_lost_in_bdd_closure_2026-06-29.md`.

**lib/common after both fixes:** 484 pass / 125 fail / 23 err (23 err = WARN/INFO
noise). Decisive breakdown of the 125 remaining FAIL files:
- **~62 `wine_*`** (wine_process 29, wine_dll 12, wine_kernel32_* 6, wine_nt/ntdll 7,
  wine_hello 3, …): **59 are "function not found"** — a test-first Windows
  PE-loader / NT / kernel32 / ntdll emulation suite with **no implementation**.
  NOT bugs; implementing them is a large unrequested feature.
- **~18 other missing-symbol**: `set_utils`/`iterable`/`functions` modules were
  **deliberately deleted** (commit "Track production readiness convergence");
  the specs (incl. `deprecated_removed_spec`, `iter_deprecated_spec`) are **stale**
  → removal needs approval, not restore.
- **~45 genuine value-mismatch**: encoding cluster now FIXED; `lshr/overflow_debug`
  are scratch specs expecting logical `>>` when i64 `>>` is correctly arithmetic
  (spec wrong, not a bug); the rest is a long individual tail (each its own
  investigation).

**Conclusion:** the two systematic clusters (BDD matcher + cross-module array
write-back) are fixed. The literal "fix ALL" is blocked by: unbuilt features
(Wine), deliberately-removed-API stale specs (approval to delete), and a
heterogeneous individual tail — no third silver bullet.

## Update #2 — "fix all" goal continuation: clean library bugs + harness finding

Banked clean, verified library fixes (each spec 0 failures after):
- **`persistent_map.from_dict`** — iterated `for k in d:` (which yields
  `(key,value)` tuples) and did `result.set(k, d[k])`, dropping every entry.
  Fixed to `d.keys()`. 64 examples → 0 failures.
- **`math_repr._greek_unicode`** — `to_pretty()` left omicron/partial/varepsilon/
  vartheta/varkappa/varphi/varpi unconverted. Added them. tokenizer spec → 0.
- (encoding msgpack/bson/cbor from Update #1.)

**Major harness bug — now FIXED (commit: test-runner preprocess):** the
interpreter test path (daemon child `test_runner_single` + `run_test_file_interpreter`)
now rewrites legacy word-infix `expect X to_equal Y` → method form before
`simple run`, mirroring the Rust batch path. privilege group/principal/id_path
now pass under `bin/simple test` (were false-red); encoding/math_repr/
persistent_map unchanged. Follow-up: this makes 4251 previously-dropped
assertions (155 files) actually evaluate — re-measure with `bin/simple test` to
get the true count (some hidden false-greens will surface as real failures).

**Original finding (filed:
`doc/08_tracking/bug/harness_word_infix_expect_not_preprocessed_2026-06-29.md`):**
legacy word-infix `expect X to_equal Y` (4251 uses / 155 files) only works when
the harness rewrites it to method form. `bin/simple run` AND `bin/simple test
<single-file>` both SKIP that rewrite, so the matcher is dropped:
- falsy-call subjects → **false-RED** (e.g. privilege/group, principal, id_path —
  the libraries are correct);
- everything else → silent **false-GREEN** (assertion never runs).
So this sweep's `run`-based PASS counts are inflated by hollow greens and the
fail counts include legacy-syntax artifacts. **Highest-leverage next step:** wire
`preprocess_matchers_only` into the single-file `test` dispatch, then RE-MEASURE
with `bin/simple test` (a `run` sweep can't validate word-infix). NOTE: doing so
will convert current false-greens into real (possibly failing) assertions.

**Residual — full triage of the 40 "genuine-fixable" candidates (clean-bug pool
is now EXHAUSTED):**
- FIXED (clean library bugs): encoding msgpack/bson/cbor, persistent_map.from_dict,
  math_repr greek. (5 this session.)
- **Unbuilt feature / changed API (NOT bugs)** — reclassified after reading source:
  - `web/browser_session_*` redirect/HEAD/303/307: NO redirect-follow, HEAD-strip,
    or 30x logic exists anywhere in the module — test-first HTTP semantics never
    built (same class as wine).
  - `win_fs/acl`: test wants `acl_check(WindowRecord, AuthorityToken, FsOp) -> bool`;
    module has `acl_check(caller: text, acl: text) -> AclDecision`. Richer API unbuilt.
- **Test-side issues (library correct):**
  - `ds_utils_stack_queue`: `pop() -> T?` returns `Some(3)`; test does
    `expect(pop()).to_equal(3)` without unwrapping → `Some(3) != 3`. Test bug.
  - privilege/group/principal/id_path + many others: word-infix harness gap (above).
- **Deep codec/compiler internals (real, multi-step each):** zstd_*/hpack/huffman,
  js_jit_optimizer, diagnostics/simple_formatter, module_import diagnostics.
- **Interpreter limitation:** fault_detection_enhanced relies on module-global
  mutation from a fn called in an it-block (writeback not persisted in BDD context).

No shared root remains; no append-helper or matcher shortcut applies. Closing the
rest requires feature implementation, approved test edits, or seed/harness work
(the word-infix fix, which will *raise* the measured failure count by exposing
false-greens — must be done deliberately and re-measured with `bin/simple test`).

## Accurate re-measurement after the harness fix (lib/common, via `test --no-session-daemon`)

`bin/simple test --no-session-daemon <file>` now preprocesses (the fix), giving a
daemon-free accurate path. lib/common: **PASS 489 / FAIL 140 / NORESULT 3**
(vs the earlier `run`-based 484/125 which mis-measured word-infix).
- 5 specs flipped false-RED → PASS (privilege etc.).
- 20 specs flipped to FAIL: ~12 are `wine_*` that were **false-GREENING** (vacuous
  word-infix passes) and now correctly fail (still unbuilt PE-loader feature, not
  bugs); ~6 are module/symbol-resolution errors (run-based NORESULT reclassified
  as FAIL); ~3 are load-level issues. **No new fixable cluster** — confirms the
  residual is unbuilt-features + individual issues, as categorized.
- Net: the harness fix makes the suite HONEST (no silent false-greens), which is
  why FAIL rose — those were always real, just hidden.

## Fixes landed (verified)
1. **BDD matcher bug** (seed, commit `62cea5b`, rebuilt+deployed) — `expect(falsy_call()).to_matcher()`
   false-failed ("expected call result to be truthy"). Monotonic `BDD_MATCHER_RAN` flag.
   **Dominant cause: ~70% of unit-test failures.** lib/common ~32%→~10%. No false-greens
   (genuine mismatches and bare hollow `expect(call())` still fail).
2. **Encoding guard reverts** — revived 9 deleted `*_guard_spec.spl` + restored 8 sources + yaml/parse.spl.
3. **Compress guard reverts** — restored 10 sources (3 had jj conflict markers).
4. **Test-runner refuse→fallback** (commit `e17778`) — bulk runs no longer false-fail 0/N.
5. Restored deleted `bin/simple` symlink (a parallel session wiped it mid-session).

## Sweep methodology
Per-file `<release-binary> run <spec>` at `-P 16` (absolute path — symlink got clobbered once).
Excludes hidden `.spipe_*` fixture files (not standalone tests). 16,780 real spec files.
(Bulk `simple test <dir>` halts after "Session setup" — unresolved; per-file is the only reliable path.)

## FINAL full-suite results (ALL 16,780 real spec files completed)
- **PASS 13,391 (80.7%)**, FAIL 2,541, ERR 670, timeout/noresult 178.
- **FAIL+ERR = 19.3%** of files. (ERR is mostly import/JIT *warnings* masking the result + some
  real module-resolution errors; system/perf specs are environment-heavy: QEMU, Lean/Mathlib.)
- Note: `test/01_unit/*` and `test/unit/*` are parallel near-duplicate trees (similar per-dir
  failure counts), so ~half the 16,780 is duplication.
- Method: `<release-binary> run <spec>` per file, -P 16→24, 30–60s timeout, absolute binary path
  (symlink got clobbered mid-run by a parallel session and was restored).

## Failure distribution (by dir, reliable sample)
lib 319, os 143, integration/app 132, unit/app 128, compiler 73, system/app 67,
system/check 35, browser_engine 17, browser 12, formal_verification 12.

## Residual failure classes (heterogeneous — no second silver bullet)
- **Unimplemented-API specs**: e.g. `compress_utilities_spec` imports ~22 functions
  (`write_u16_le`, `decode_match_extension_length`, …) that don't exist in `compress.utilities`
  — written test-first against an unbuilt module.
- **Toolchain-dependent**: Lean/Mathlib (`expected import Mathlib...`), QEMU system specs.
- **Seed/interpreter bugs**: `with_module_name not found on dict`, i64::MIN negation overflow.
- **Slow specs** hitting the 60s per-file timeout (os/system).
- A few genuine value mismatches.

Each needs individual investigation; fixing the full ~12k baseline is multi-session work.
The one high-leverage fix (matcher) is done and resolves the largest share.
