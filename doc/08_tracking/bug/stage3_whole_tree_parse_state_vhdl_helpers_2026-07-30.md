# Stage-3 whole-tree build mis-parses vhdl_codegen_helpers.spl (parser STATE, not grammar)

**Found:** L7 run 9 (2026-07-30), faithful stage-3 invocation on origin
`110f743b2a2`, cranelift, `--entry-closure --mode one-binary`.
**Status:** Open, and the repro is FLAKY, not deterministic — see "2026-07-30
investigation" below. Three independent, clean-cache runs of the exact repro
command on the exact pinned commit (`110f743b2a2`, hermetic worktree
`simple_l7_wt`, same prebuilt stage-2 binary as run 9) all **succeeded** with
0 parser errors. A real, separate defect (duplicate parsing of the same file
via its symlink spelling) was found by static tracing and is documented below
with file:line evidence, but it could NOT be confirmed as run 9's actual
trigger because the failure would not reproduce to test the fix against.
Still blocks stage 3 / L7 / Stage-4 until either the failure reproduces again
(e.g. under concurrent machine load) or the symlink-duplication defect is
fixed and shown to matter.

## 2026-07-30 investigation (this session)

**Reproduction attempts: 3/3 clean-cache runs succeeded (could NOT reproduce the 45 parser_errors).**

Ran the doc's exact repro command in `simple_l7_wt` (clean worktree, detached
at `110f743b2a2`, same prebuilt
`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` binary run 9 used):

```
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build \
  --target x86_64-unknown-linux-gnu --backend cranelift \
  --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/app --source src/lib --source examples/10_tooling \
  --entry-closure --low-memory --threads 8 --mode one-binary \
  --entry src/app/cli/main.spl --runtime-path src/compiler_rust/target/bootstrap -o <out>
```

| Run | Cache state | `SIMPLE_COMPILER_TRACE` | Result | `grep -c parser_error` |
|---|---|---|---|---|
| build2 | empty (first use) | `=1` | `Build complete: 1494 compiled, 0 cached, 0 failed` | **0** |
| build3 | warm (reused build2's `.simple/native_cache`) | unset | `Build complete: 4 compiled, 1490 cached, 0 failed` (not a clean test — see below) | **0** |
| build4 | cleared with `rm -rf .simple/native_cache` right before the run | unset | `Build complete: 1494 compiled, 0 cached, 0 failed` | **0** |

build2 and build4 are the load-bearing runs: both compiled all 1494 modules
fresh (0 cached) and both finished cleanly. `git status --short` in the
worktree was empty before and after (no accidental local edits). Per the
method rule "if you cannot reproduce, say so and stop" — this is reported
as-is rather than a fabricated root cause.

**Discovery: `.simple/native_cache` is a content-hash-keyed object-code cache,
not a source/AST cache** (`.o` files under `objects/`, keyed by hash,
`incremental_manifest.txt` alongside). A cache hit skips recompiling a file
entirely, so build3 (1490 cached) exercised the parser for only 4 files and
tells us nothing about the bug — noted here so a future session doesn't reuse
it as evidence either way.

### A real, separate defect found by static tracing: `vhdl_codegen_helpers.spl` is loaded and parsed TWICE, under two different (path, module_name) pairs, via its symlink spelling

Chain of evidence (file:line, no dynamic confirmation since the failure did
not reproduce to test against):

1. `src/compiler/backend` is a symlink to `70.backend`
   (`src/compiler/backend -> 70.backend`, confirmed with `ls -la`/`readlink -f`).
   Plain `find src/compiler -type f -name '*.spl'` — used by
   `_driver_collect_sources` (`src/compiler/80.driver/driver_source_loading.spl:860`)
   for the `--source src/compiler` bulk scan — does **not** follow that
   symlink, so the bulk scan finds only the real spelling:
   `src/compiler/70.backend/backend/vhdl_codegen_helpers.spl` (verified:
   `find src/compiler | grep vhdl_codegen_helpers` returns exactly one path,
   the real one).
2. Several files under `70.backend/backend/` import a sibling via the
   **absolute dotted** form with the tier-stripped-but-still-doubled segment
   `compiler.backend.backend.X`, e.g.
   `src/compiler/70.backend/backend/_VhdlProcess/process_codegen.spl:12`,
   `src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl:19`,
   `src/compiler/70.backend/backend/_VhdlProcess/terminator_codegen.spl:12`,
   and `src/compiler/80.driver/driver_aot_vhdl_output.spl:12` all write
   `use compiler.backend.backend.vhdl_backend...`.
3. `run_focused_native_build_plan` (`src/app/cli/bootstrap_focused_native_build.spl:74`)
   — the actual dispatch target of `native-build --entry-closure` (confirmed:
   its error format string `"error: focused native-build: {err}"` at line 114
   matches the doc's `[ERROR] ... error: focused native-build: parse error in
   ...` symptom exactly) — sets
   `env_set("SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE", "0")` before calling into the
   driver, and restores the caller's value only afterward. This forces the
   phase-1 **import-closure walker**
   (`driver_source_pipeline_loading.spl:163-254`, gated on
   `nb_entry_env != "" and not nb_entry_closure_pre`) to run — the walker
   textually scans every already-loaded file's `use` lines
   (`_driver_entry_import_module_paths`) and resolves each to a file via
   `_driver_resolve_entry_import` → `_driver_try_entry_import_rel`
   (`driver_source_loading.spl:528-540`), which tries `"src/" + rel + ".spl"`
   **before** the tier-numbered fallback
   (`_driver_resolve_numbered_compiler_import`). For
   `compiler.backend.backend.vhdl_backend` this succeeds via the symlink,
   producing `src/compiler/backend/backend/vhdl_backend.spl` — the SYMLINK
   spelling, loaded as a brand-new `SourceFile` distinct from the
   already-scanned real-spelling copy (different `path`, and a different
   `module_name` since `_driver_module_name_from_path` is purely lexical:
   `compiler.backend.backend.vhdl_backend` vs.
   `compiler.70.backend.backend.vhdl_backend`).
4. `vhdl_backend.spl` itself does `use .vhdl_codegen_helpers.*` — a
   **relative** import (`src/compiler/70.backend/backend/vhdl_backend.spl:24`).
   The closure walker resolves relative imports against the *importing
   file's own path*, so when the walker processes the symlink-spelled copy of
   `vhdl_backend.spl` from step 3, this relative import resolves to
   `src/compiler/backend/backend/vhdl_codegen_helpers.spl` — again the
   SYMLINK spelling, exactly the path in the doc's `[parser_error]` lines.
5. None of the closure walker's dedup structures catch this: `seen_sources`
   is keyed by `path + "::" + module_name` (both differ from the real-spelling
   entry); `closure_loaded_mods` is keyed by `module_name` (also differs).
   The one dedup that *does* resolve symlinks,
   `_driver_physical_source_key` (`rt_path_absolute`, i.e. `realpath`), is
   only used at `driver_source_pipeline_loading.spl:198` to avoid re-scanning
   a file's own import list twice — never to dedup which files get added to
   `all_sources`.
6. By phase 2 (`parse_all_impl`,
   `driver_source_pipeline_parsing.spl:119-196`),
   `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE` has been flipped back to `"1"`
   (`driver_source_pipeline_loading.spl:254`), so every source — both
   spellings of `vhdl_codegen_helpers.spl` — passes the `entry_sources`
   filter. `_driver_unique_physical_sources`
   (`driver_source_loading.spl:171-182`) dedups only via
   `_driver_canonical_source_path`, which is **lexical** normalization of
   `.`/`..` segments — it never calls `rt_path_absolute`/`realpath`, so it
   does not collapse the two spellings. Both remain in
   `unique_entry_sources` and are handed to two independent
   `parse_full_frontend` calls
   (`driver_source_pipeline_parsing.spl:156-161`) — the file is parsed twice.

**Hypothesis 1 (byte-slicing) — DISPROVEN.** Both spellings resolve (via the
symlink) to the same inode; content is read whole-file via
`rt_file_read_text(p)` in both `_driver_collect_sources` and
`_driver_collect_entry_import_source` — no region-slicing exists anywhere in
this path. Confirmed on disk: both spellings are 16922 bytes, identical
md5 (`63217ce79dc986590eb9c3350058ef73`).

**Hypothesis 2 (double registration via the symlink) — CONFIRMED AS A REAL,
DETERMINISTIC DEFECT by static tracing (steps 1-6 above), but NOT CONFIRMED
as run 9's trigger** — double-parsing identical content twice, by itself,
did not corrupt anything in 3 clean runs of this exact commit/binary.
Note `--threads 8` is a dead flag on this path: it is never read by
`bootstrap_focused_native_build_args.spl` or `bootstrap_focused_native_build.spl`
(grepped, no hits), and `driver_build/parallel.spl`'s process-pool parallelism
(explicitly process-based, not thread-based, "to avoid thread-safety issues
with global compiler state" per its own header comment) is not wired into
this code path either — so there is no in-process concurrency to race on the
env-var-backed lexer globals (`lex_state_get`/`lex_state_set`,
`src/compiler/10.frontend/core/lexer.spl:191-217`) during phase 2 parsing.
The double-parse is therefore two purely *sequential* calls to
`parse_full_frontend` on identical bytes, which the per-source lexer reset
(`src/compiler/10.frontend/core/lexer.spl:130-173`, called before each file)
should make order-independent. Either (a) something not yet found makes the
two sequential parses interact anyway (e.g. hypothesis 3's fixed-size side
tables accumulating across the *whole* tree, where the extra duplicate
parses from this same defect — likely affecting more files than just this
one, anywhere a symlinked tier directory is combined with a double-segment
absolute import — could tip a silent-truncation threshold that only bites
under the right module count/order), or (b) run 9 hit a different,
still-unidentified trigger, possibly related to the sibling `gdb`-wrapped
stage-3 build this session observed running concurrently on the same
machine for the entire duration of all 3 repro attempts (separate process,
separate env — no obvious shared-state channel found, but machine-level
resource contention during a memory/CPU-heavy compile was not ruled out).

**Hypothesis 3 (capacity exhaustion in a fixed-size side table) — NOT
FURTHER INVESTIGATED.** Still open; not reached because there was no
reproduced failure to instrument.

**Proposed fix (NOT applied — unverifiable without a reproduced failure to
test against, and touches driver code shared by every native-build
invocation):** in the phase-1 closure walker
(`driver_source_pipeline_loading.spl:163-254`), key `closure_loaded_mods`
(and the `seen_sources`/alias bookkeeping around it) by
`_driver_physical_source_key(closure_file)` in addition to `closure_mp`, so a
file already loaded under one spelling is recognized when reached again
under another. This is a real, deterministic, independently-worth-fixing bug
regardless of whether it explains run 9 — it duplicates parse+compile work
for every file reachable through a symlinked tier directory via an absolute
double-segment import, and the code's own comments already warn duplicate
aliases feeding Phase 3 causes "duplicate-HIR / duplicate-diagnostics"
regressions (`driver_source_loading.spl:213`).

**Recommended next step:** retry the repro while the machine is under
concurrent load (e.g. run alongside another build, matching the conditions
present during run 9 — this session observed a second, unrelated stage-3
build running under `gdb` in `/home/ormastes/dev/pub/simple` for the entire
duration of all 3 repro attempts, so "concurrent load" was in fact present
and still didn't reproduce it, which weakens but doesn't eliminate a
contention-based explanation). If it reproduces, capture the parser state
(indent stack, current token) at the moment of failure before touching
anything else.

## Original findings (pre-2026-07-30 investigation, unchanged)

Supersedes `stage2_parser_result_unit_generic_divergence_2026-07-29.md`,
whose grammar diagnosis is retracted (see that doc).

## Symptom

45 `[parser_error]` lines, ALL in a single file, reached through the symlink
path spelling:

```
[parser_error] path src/compiler/backend/backend/vhdl_codegen_helpers.spl line 201:13: expected :, got Ident 'arg_exprs'
[parser_error] path .../vhdl_codegen_helpers.spl line 201:13: expected Indent, got Ident 'arg_exprs'
[parser_error] line 202:1: unexpected token in expression: Dedent ''
[parser_error] path .../vhdl_codegen_helpers.spl line 207:122: expected :, got Ident 'CompileError'
[ERROR] phase 4 FAILED
error: focused native-build: parse error in src/compiler/backend/backend/vhdl_codegen_helpers.spl
```

First failure is line 201 (`arg_exprs = arg_exprs.push(arg_expr)`), i.e. the
statement immediately AFTER a `match` block's last arm. The parser was still
expecting another `case … :` and choked on the dedent. Everything after
(including the line-207 signature) is cascade.

## What is NOT the cause — each measured, not inferred

Method: parse with a real stage-2 pure-Simple binary
(`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build`).

| Candidate | Result |
|---|---|
| `fn f() -> Result<(), text>:` (unit type in generic args) | parses clean, exit 0 |
| `match if c: a else: b:` (inline if as match subject) | parses clean, exit 0 |
| Exact failing block (class + method + `for` + `match if` + `case Err(e): return Err(e)`) | parses clean, exit 0 |
| The ENTIRE victim file, in isolation, @origin | zero `parser_error`; reaches HIR |
| The ENTIRE victim file, in isolation, @run-8 pin `38cb691ad082` | zero `parser_error`; byte-identical to origin |
| Victim parsed after a 400-line pad file (position accumulation) | zero `parser_error` |
| Victim reachable through a symlinked alias directory | zero `parser_error` |
| `SIMPLE_AST_GEN_CHECK=1` stale-generation / OOB diagnostics during the failing run | **0** |

So: the grammar accepts every construct in the file, and the file parses
clean by itself at both trees. The failure exists ONLY in the whole-tree
focused build.

## Leading hypotheses (untested)

1. **Focused/entry-closure partial parse.** Phase 4 is a "focused"
   native-build driven by `--entry-closure`. If focused mode parses a
   SUBSET of a file (only entry-reachable functions), a region sliced
   mid-file would start with the wrong indentation baseline — which matches
   the symptom exactly (`expected Indent`, `unexpected Dedent`, arms not
   terminating).
2. **Double registration via the symlink spelling.** `src/compiler/backend`
   is a symlink to `70.backend`, so the same file is reachable under two
   module names (see memory `reference_compiler_symlink_module_spellings`).
   A second parse reusing first-parse arena/lexer state would corrupt
   block structure. Note the error path uses the SYMLINK spelling, so the
   symlink pass is the one that failed.
3. **Capacity exhaustion in a fixed-size parser side table.** Whole-tree
   parsing fills the named-type / tuple / isolated-type registries that
   `parser_parse_type_impl` consults; a silent overflow would degrade
   parsing only at scale. `tuple_type_register` has an explicit
   `< 0` overflow path, so check the others for silent truncation.

## Repro

```
# fails (~7 min):
cd <worktree at origin>
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build \
  --target x86_64-unknown-linux-gnu --backend cranelift \
  --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/app --source src/lib --source examples/10_tooling \
  --entry-closure --low-memory --threads 8 --mode one-binary \
  --entry src/app/cli/main.spl --runtime-path <wt>/src/compiler_rust/target/bootstrap -o /tmp/out.bin

# passes: same binary, same file, isolated source dir
```

`--entry-closure` is required to reproduce the build at all: without it the
multi-root scan aborts earlier on a module-name collision
(`src/app/__init__.spl` and `src/compiler/__init__.spl` both sanitize to
`__init__`) — worth fixing separately, since it makes non-closure whole-tree
builds impossible.

### UPDATE 2026-07-30: `__init__` collision already fixed, not re-fixed here

Investigated as a separate lane. Findings:

- **Root cause was entirely in the Rust seed**, not the pure-Simple driver.
  `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`
  (`effective_source_root_for` + `module_prefix_from_path`, used by the
  non-entry-closure collision check around line 680) picked, per FILE, the
  *deepest matching* `--source` root and relativized the module name against
  just that root. With sibling roots `src/app` and `src/compiler` both
  passed via `--source`, each file's own root swallowed the very segment
  (`app` vs `compiler`) that would have disambiguated it, so both
  `__init__.spl` files relativized to bare `__init__`.
- **This is already fixed** in the current tree by commit
  `4c4e98e18c4` ("fix(native-build): multi-root source dirs no longer
  collide on module name", landed 2026-07-29, before this investigation
  started). `effective_source_root_for` now relativizes against the common
  ancestor of all valid `--source` dirs whenever more than one is real,
  which keeps the disambiguating segment. The file is clean in the working
  copy (not concurrently edited by another lane).
- **The pure-Simple mirror never had this defect.**
  `_driver_module_name_from_path` in
  `src/compiler/80.driver/driver_source_loading.spl` does not relativize
  per `--source` root at all — it strips one fixed leading `src/` segment
  regardless of which root a file was discovered under. Verified directly:
  `_driver_module_name_from_path("src/app/__init__.spl")` → `app.__init__`,
  `_driver_module_name_from_path("src/compiler/__init__.spl")` →
  `compiler.__init__` (distinct, no collision). No `.spl`-side change was
  needed or made.
- **Verified against the literal repro command** (no `SIMPLE_BOOTSTRAP_STAGE4`
  set, so it runs through the Rust `rt_native_build` FFI seed exactly as the
  original repro did) with `SIMPLE_NATIVE_BUILD_RUST_TRACE=1`: it discovered
  11484 files across all four `--source` roots (`src/compiler`, `src/app`,
  `src/lib`, `examples/10_tooling`) and printed no
  `native module name collision` error, proceeding straight into
  compilation (the run was then stopped by an outer 60s timeout during
  actual codegen, not during file discovery/collision-checking, which is
  the first phase after discovery).
- `test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl`
  → `it "rejects distinct physical files with one sanitized module name"`
  passes, confirming `_driver_module_name_collision` itself still correctly
  flags real collisions (fail-closed, not fail-open) on the `.spl` side.
- Ordinary module names are unaffected/unchanged (spot-checked via
  `_driver_module_name_from_path`):
  `src/compiler/80.driver/driver_source_loading.spl` →
  `compiler.80.driver.driver_source_loading`; `src/app/cli/main.spl` →
  `app.cli.main`; `src/lib/common/string_core.spl` → `lib.common.string_core`.

No code change made in this update — this section only corrects the
now-stale "worth fixing separately" note above so a future reader doesn't
re-open a defect that no longer exists. `src/compiler_rust/**` is out of
scope for this lane regardless (owned by other concurrent lanes per
session policy).

## Next step (superseded by the 2026-07-30 investigation above)

~~Bisect hypothesis 1 first (cheapest, best symptom match): dump the exact
source text the focused path hands the lexer for this module and compare it
byte-for-byte with the file on disk.~~ Done 2026-07-30: hypothesis 1 is
disproven (no slicing occurs; both spellings feed the lexer identical
whole-file bytes). The open question is now why 3 clean repro attempts all
passed — see "Recommended next step" in the 2026-07-30 section above (retry
under concurrent load; instrument hypothesis 3's side tables if it
reproduces).
