# Coverage-wrapper `Undefined("undefined identifier: X")` — root-cause grouping

Date: 2026-08-31
Status: PARTIALLY FIXED (cause B fixed at 5 sites; causes C, D, E, F open)
Correction 2026-08-31: cause A ("stale deployed seed") is RETRACTED as factually
wrong — see that section. The cause-B fixes stand and are now verified against
the exact binary that produced the log.
Evidence base: `/tmp/suite3.log` (1365 PASS / ~220 FAIL), 69 wrapper compile
failures across 26 distinct symbol names, 100 unique (symbol, spec) pairs.

## Method — and why the log's census is misleading

The failures are reported against the generated native entry
`/mnt/data/tmp/spipe_wrapped__..._spec_native.spl`, but the error message names
only the ROOT compile unit, never the module the bad identifier is actually in.
Every symbol below was located by bisecting the import closure with minimal
probe files (`use <module>` + `fn main()`) and reading `bin/simple compile`'s
own exit status — not the test-runner verdict.

Crucially, the failures are LAYERED: one module can hide several. Fixing
`io_runtime` in `env/variables.spl` immediately exposed `text_byte_len`, which
had never appeared in the log at all. The 26 names in the log are therefore a
LOWER BOUND, not the population.

## Cause A — RETRACTED 2026-08-31: "stale deployed seed" was WRONG

**This section originally claimed the suite3 census was produced by a seed
predating the `panic` builtin fix `777f3c99583`, and advised a redeploy. That is
false and the advice would have wasted the next person's time. Retracted in
full; the reasoning error is kept below so it is not repeated.**

Actual binary identity:

| binary | size | mtime (UTC) | built from |
|---|---|---|---|
| `/mnt/data/wt-suite/bin/release/x86_64-unknown-linux-gnu/simple` — **this is the one suite3 used** | 60976360 | 2026-08-31 10:45:20 | `b0be388ec46`, built that morning |
| `/mnt/data/worktrees/simple-main/bin/simple` — the one I inspected | 60744944 | 2026-08-26 01:16:25 | older |

suite3 ran `./bin/simple test --no-cover-check` with cwd `/mnt/data/wt-suite`,
so it used the first. That binary already contained everything on `main` through
`#157`, including `777f3c99583` (2026-08-30). **The seed was current.** I read
the mtime of a binary in a different worktree and never checked which one the run
actually used — the whole cause was an artifact of that.

**Strongest evidence, found last:** the suite3 pipeline was still running during
this correction, and its own command line settles it — the seed is built and
installed *in the same shell pipeline as the test run*, immediately before it:

```
cd /mnt/data/wt-suite/src/compiler_rust && CARGO_TARGET_DIR=/mnt/data/cargo-targets-suite \
  cargo build --release --bin simple \
  && cp /mnt/data/cargo-targets-suite/release/simple \
        /mnt/data/wt-suite/bin/release/x86_64-unknown-linux-gnu/simple.new \
  && mv /mnt/data/wt-suite/bin/release/x86_64-unknown-linux-gnu/simple.new \
        /mnt/data/wt-suite/bin/release/x86_64-unknown-linux-gnu/simple \
  && cd /mnt/data/wt-suite && SIMPLE_TIMEOUT_SECONDS=0 ./bin/simple test --no-cover-check
```

That is a build-then-run pipeline over `/mnt/data/wt-suite`, so the seed cannot
have been stale relative to that tree by construction — no mtime comparison is
even needed. It also shows `--no-cover-check` and `SIMPLE_TIMEOUT_SECONDS=0`,
neither of which I replicated when trying to reproduce (relevant to cause F
hypothesis 2 below).

Two further facts confirm the retraction:

- `panic` appears **zero** times in suite3's symbol census. Had the run used a
  seed predating `777f3c99583`, `panic` would have been the dominant symbol —
  its absence is positive evidence the fix was present.
- Re-running the probes directly on `/mnt/data/wt-suite`'s binary in its own tree
  reproduces the cause-B symbols exactly (see below). Nothing needed a redeploy.

Consequences for the rest of this document:

- "an unknown fraction of the 69 is already fixed at origin" — **withdrawn**, not
  supported by anything.
- Symbols parked under cause A on the strength of "probably already fixed" are
  re-classified into **cause F** below. None of them were shown to be fixed.

**What survives, and is worth keeping:** use a binary built from the revision
under test as the discriminator, and record its identity (path, size, mtime,
source commit) alongside any timing or verdict — not the mtime of whatever
`bin/simple` happens to point at in some other worktree. That advice is right; it
simply was not violated by the suite3 run.

## Cause B — undeclared cross-file use (FIXED, 5 sites)

A module calls a symbol that is defined in a *sibling* file with no `use` and
no local `extern fn`. The interpreter's program-wide, name-keyed function table
resolves it anyway; whole-program semantic analysis on the native path does not.

| site | symbol | fix |
|---|---|---|
| `src/lib/nogc_sync_mut/env/variables.spl:63` | `io_runtime` (module alias — `use std.io_runtime` does not bind the trailing segment) | selective aliased import |
| `src/lib/nogc_sync_mut/lsp/lsp_protocol.spl:65` | `text_byte_len` (in sibling `lsp_json.spl`) | added `use` |
| `src/lib/nogc_sync_mut/lsp/lsp_protocol.spl:67,68` | `print_raw` (in `sffi/diag.spl`) | added `use` |
| `src/os/crypto/aes256_gcm.spl:643` | `rt_tls13_aes256_gcm_encrypt` (declared only in `os/apps/sshd/ssh_cipher_live.spl`) | added local `extern fn` |
| `src/lib/nogc_sync_mut/compression/gzip/compress.spl:623` | `gzip_stream_compress` (in sibling `stream.spl:83`) | added `use` |

Before/after proof, fresh seed, `use std.nogc_sync_mut.env.variables`:
- before: `Undefined("undefined identifier: io_runtime")`
- after: no `Undefined`; fails later on the pre-existing, unrelated
  "cannot compile to standalone SMF: 32 function(s) require the interpreter".

### Reproduced on the exact binary that produced the log (added 2026-08-31)

After the cause-A retraction the fixes were re-verified against
`/mnt/data/wt-suite/bin/release/x86_64-unknown-linux-gnu/simple` — the binary
suite3 actually ran — invoked in its own unmodified tree at `b0be388ec46`:

| probe | result on the suite3 binary |
|---|---|
| `use std.nogc_sync_mut.env.variables` | `Undefined("undefined identifier: io_runtime")` |
| `use std.nogc_sync_mut.lsp.lsp_protocol` | `Undefined("undefined identifier: io_runtime")` |
| `use os.crypto.aes256_gcm` | `Undefined("undefined identifier: rt_tls13_aes256_gcm_encrypt")` |
| `use std.nogc_sync_mut.compression.gzip.compress` | `Undefined("undefined identifier: gzip_stream_compress")` |

So cause B is a genuine latent defect on the log-producing binary, established
without reference to any redeploy story. This is stronger evidence than the
original write-up had.

### Scope of this proof — read before quoting a cluster size

The before/after above is on a **probe file**, not on a generated wrapper. An
attempt to close that loop produced an honest negative and it is recorded here
rather than omitted: running
`SIMPLE_MCDC_MODE=on bin/simple test test/feature/scilib/linalg_norm_spec.spl
test/feature/lib/mcp/handler_registry_spec.spl --coverage` (one spec from the
`io_runtime` cluster, one from the `print_raw` cluster) on the fresh seed gives
`PASS` for both **with the fix applied AND with it reverted**, with zero
`[mcdc-fallback]` lines and zero `undefined identifier` in either run.

The obvious confound — a wrapper build-cache hit carrying the fixed run's SMF
into the reverted run — was checked and ruled out: the reverted run was repeated
with `--force-rebuild` and still PASSes with zero `undefined identifier` and zero
`[mcdc-fallback]`.

Since PR #157 a coverage run whose wrapper will not compile is an ERROR, so a
clean PASS with no fallback means the wrapper compiled — in both states. Two
conclusions follow, and neither may be skipped:

1. The four fixes are **real and independently proven** at the module level;
   the probe before/after is unambiguous.
2. The **mapping from a fixed site to a wrapper count is NOT established.**
   `env/variables.spl` is in nearly every spec's *runtime* closure, but that is
   not the same set as a wrapper's *compile* closure, and the experiment above
   is direct evidence they differ. The "18 wrappers" figure is the suite3 log's
   symbol count, not a measured effect of this fix. Do not quote it as one.

Reproducing a failing wrapper on demand is the missing capability here. The
runner deletes the artifact on success and `--keep-artifacts` did not preserve
one in these runs; a way to retain the generated wrapper unconditionally would
have made this a one-command check and should be added.

## Cause C — colliding module-private names across files (FILED, needs a decision)

`src/os/crypto/aes256_gcm.spl:670` calls `_append_bytes` with **no definition in
the file**. `_append_bytes` has **11 distinct definitions** across the tree with
*different signatures* — some return `[u8]`, some mutate in place and return
nothing (`os/apps/sshd/ssh_mac.spl:16`,
`lib/nogc_sync_mut/composition/codec.spl:164`). The seed already warns about
this class:

```
warning: public function `env_get` has 3 co-compiled definitions with 2 differing
signatures ...; falling back to the last definition when types are ambiguous
[compiler_cross_module_private_symbol_collision]
```

Same shape, unresolved: `_u8_at` (3 defs), `_inc32` (2 defs), `alloc` (2 defs),
`Platform` (2 conflicting `enum` declarations — `lib/nogc_sync_mut/package/dist.spl:19`
and `compiler/70.backend/linker/smf_enums.spl:18`).

**Not fixed here on purpose.** Picking a definition for `aes256_gcm.spl` is a
correctness decision about crypto code (return-a-copy vs mutate-in-place), and
adding a 12th local definition makes the collision worse. The `Platform` enum
duplication needs an owner to say which is canonical. This blocks the 7
`rt_tls13_aes256_gcm_encrypt` specs even with the Cause-B fix applied — the
extern declaration is correct and necessary, but `_append_bytes` surfaces
immediately behind it.

## Cause D — class-scope plain `fn` invisible to sibling methods (FILED)

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:207` declares
`fn folded_global_scalar_type(...)` INSIDE a class body (indented alongside `me`
methods) and calls it unqualified from `me` methods at `:225` and `:399`.
Accounts for the 5 `folded_global_scalar_type` wrappers (llvm/wasm backend
specs).

Two candidate fixes, hence filed rather than guessed: hoist it to module level
(behaviour-identical — it takes no `self`), or make the seed's checker resolve
class-scope associated functions from sibling methods. The second is the real
language question and should be answered before the first is applied as a
workaround.

## Cause E — genuinely missing symbols (FILED)

`_pmm_reset_contiguous_registry` (called at `src/os/kernel/memory/pmm.spl:116`
and `:256`) and `rsa_sha512_sign_embedded_host` have **no definition anywhere in
the tree**. These are not resolution bugs; the functions do not exist. Owner
input needed on whether they were dropped by a bad merge or never written.

## Unclassified residue

Probes already run on the fresh seed, recorded so they are not repeated:

| probe | result | reading |
|---|---|---|
| `use lib.sdn` | clean on **both** my seed and the suite3 binary | `String` (8) / `Dict` (6) / `value` (6) do **not** come from `src/lib/sdn/__init__.spl`'s unqualified `case String(s)` / `case Dict(entries)` patterns, which was the leading hypothesis. With cause A retracted these are **unlocated**, not fixed — see cause F. |
| `use std.nogc_sync_mut.package.dist` | clean | `Platform` not reproduced from this side |
| `use compiler.backend.linker.smf_enums` | clean | `Platform` not reproduced from this side either |
| `use std.nogc_sync_mut.composition.codec` | clean | — |
| `use std.nogc_sync_mut.compression.gzip.compress` | `Undefined("undefined identifier: gzip_stream_compress")` | live cause B — **now fixed** |

## Cause F — real in suite3, not reproducible by any probe (OPEN, needs the wrapper)

`String` (8), `Dict` (6), `value` (6), `NativeTensor`, `Node`, `fs`, `temp_dir`,
`float`, `raise`, `alloc`, `shared_examples`, `context_def`, `async_mode`,
`mul_scalar`, `_b64_index`.

These were previously parked under cause A on the assumption they were already
fixed. **That assumption is withdrawn and nothing replaces it.** What is known:

- They appear in suite3's log, produced by a `b0be388ec46` binary.
- Probing their most likely owning modules with that same binary compiles clean.
- Two specs drawn from the log's failing set (`scilib/linalg_norm_spec.spl`,
  `lib/mcp/handler_registry_spec.spl`) now PASS under
  `SIMPLE_MCDC_MODE=on ... --coverage --force-rebuild`, with and without the
  cause-B fix.

So the failures are real but **not reproducible outside the suite3 run** by any
method available here. Candidate explanations, none of which is established and
none of which should be written up as fact until a wrapper is in hand:

1. The generated wrapper's compile closure genuinely differs from a plain
   `use <module>` probe's closure (the flat `fn main()` restructuring in
   `spipe_*` moves declarations between scopes).
2. Run-state not replicated. The suite3 command line (captured above) is
   `SIMPLE_TIMEOUT_SECONDS=0 ./bin/simple test --no-cover-check` from cwd
   `/mnt/data/wt-suite` — a whole-suite run. My reproduction attempts passed
   two explicit spec paths with `--coverage` from a different worktree and set
   neither `--no-cover-check` nor `SIMPLE_TIMEOUT_SECONDS`. Whole-suite vs.
   two-spec invocation is itself an unexcluded difference, on top of cwd,
   concurrency and `TMPDIR` contents.
3. Cross-run interference in the shared temp dir — every wrapper is written to
   `_tp_get_temp_dir()` (here `/mnt/data/tmp`) under a spec-derived name, with no
   per-run isolation. Wrappers from other concurrent sessions were observed
   appearing there during this investigation.

**The blocker is the same in all three cases: no failing wrapper is retained.**
See the retention gap filed alongside this document. Until one can be captured,
these symbols should not be worked — locating them by grep alone is what produced
the retracted cause A.

Full (symbol, spec) map extracted from suite3 is reproducible with:

```
grep -oE 'spipe_wrapped__[A-Za-z0-9_]+_spec_native\.spl\): semantic: [^ ]+ Undefined\("undefined identifier: [A-Za-z_0-9]+' /tmp/suite3.log
```

These must be re-censused against a freshly built seed before any are worked:
Cause A means an unknown fraction of them are already fixed at origin.

---

## Cause F — RESOLVED 2026-08-31 (round 2). It was never a wrapper-only effect.

Status: the three largest clusters (`value` 14, `String` 8, `js_nan` latent) are
**located and fixed**. Cause F was not a distinct cause at all: it is ordinary
cause B/E in modules **nobody had probed**. The previous round probed `lib.sdn`,
`package.dist` and `smf_enums` — guesses — got clean results, and concluded the
failures were unreproducible. They reproduce on the first try against the
correct modules.

### What made them findable: containment, computed before theorising

| symbol | count | containment |
|---|---|---|
| `value` | 14 | **100%** JS-engine subtree (`browser_engine/*`, `lib/js/*`, `js_engine/*`) |
| `String` | 8 | **100%** `test/00_formal_verification/compiler/` |
| `Dict` | 6 | 5/6 `lib/gc_sync_mut/db/` |

100% containment refutes a global cause (a wrapper-generator defect would be
spread across the suite). That single computation redirected the search from the
generator to the subtrees, and each subtree's own module then failed a plain
`use <module>` probe immediately.

### Discriminator (unchanged, and it is the whole method)

`bin/simple compile <probe>.spl`, exit status read into a variable on the **next
line**, never through a pipe. Probes bisect the import closure mechanically —
every `*.spl` in the subtree is probed as `use <module>` + `fn main()`, and only
modules whose output contains the exact symbol are HITs.

### Sites fixed

| site | symbol | defect | fix |
|---|---|---|---|
| `src/lib/nogc_sync_mut/js/engine/interpreter_async.spl:587` | `value` | **stray orphaned statement.** `me _filter_request_headers(headers_text: text) -> text` ends with the real return `kept.join("\n")` followed by a leftover `js_to_string(value)`. The method has no `value` in scope. Being last, the stray line was also the actual return value — so this was a live behavioural bug, not only a compile error. | delete the stray line |
| `src/lib/nogc_sync_mut/js/engine/interpreter_types.spl` | `js_nan` | calls `js_nan()` with no `use`; the `common/` sibling has `use std.common.js.engine.js_error.{js_nan, ...}` at line 6. Textbook cause B. | add the matching `use` |
| `verification/lean/{functions,types,memory_safety}.spl` (10 sites) | `String` | `String.from_char_code(123/125)`. **No `String` type exists in Simple** (`text` does), and no `from_char_code` is defined on it anywhere — cause E, not a resolution bug. The author's intent was a literal `{` / `}`. | `"{{"` / `"}}"`, verified by running a probe: they render `{` and `}` |

Before/after, same binary (built from `79126c25822`, this worktree):

```
before: rc=1 std.nogc_sync_mut.js.engine.runtime :: undefined identifier: value
after:  rc=1 std.nogc_sync_mut.js.engine.runtime :: [requires the interpreter]   <- pre-existing, unrelated
before: rc=1 verification.lean.codegen :: undefined identifier: String
after:  rc=1 verification.lean.codegen :: undefined identifier: fs               <- layered, see below
```

### Layering is confirmed again — the census is a LOWER BOUND

Fixing `String` immediately exposed `fs` in the same closure, exactly as fixing
`io_runtime` exposed `text_byte_len` in round 1. Any count taken from a suite log
is a lower bound on the population, never the population.

### Hypotheses eliminated (so they are not re-run)

- **Poison-directory (#170).** Ruled out: `#170` is already contained in
  `4b4e2a304b4`, the commit suite4's binary was built from — only six commits
  (#173-#178) sit between it and `origin/main`, none of them #170. suite4's
  cause-F evidence is therefore post-fix, and the clusters survived the fix.
- **Wrapper-generator defect (doc hypothesis 1).** Refuted by containment above,
  and directly by the fact that plain `use <module>` probes with no wrapper
  involved reproduce every one of them.
- **Run-state / whole-suite invocation (hypothesis 2).** Not needed: the failures
  reproduce from a single `bin/simple compile` of a four-line probe. Recorded for
  completeness — suite4's real command line is
  `SIMPLE_TIMEOUT_SECONDS=0 ./bin/simple test --no-cover-check` from
  `/mnt/data/wt-suite` (read from `ps`, not assumed), and it passes **no**
  `--coverage`, which is one of the two variables the round-1 repro changed at
  once.
- **Cross-run temp interference (hypothesis 3).** Not needed, same reason.

### Still open after this round

- `fs` (2) — surfaced behind `String` in the verification closure. **Not the
  obvious candidate:** `regenerate/module_resolution.spl` matches a naive
  `fs\.` grep 7 times, but every hit is inside a **Lean source string literal**,
  not Simple code. Needs a real bisect, not a grep.
- `Dict` (6) — `std.gc_sync_mut.db` and `db.dbfs_engine` both probe CLEAN, so the
  owning module is elsewhere in those specs' closure.
- `print_raw` (8) — four specs (`host/io/stdio_async`, `mcp_jj/tools/git_branch_args_extraction`,
  `mcp/handler_registry`, `mcp/integration`). PR #154 fixed `sffi/diag.spl`
  shadowing the prelude builtin; whether this is the same defect at a second
  site is **unverified** and must not be assumed.
- Causes C (`_append_bytes` 11 conflicting defs, `Platform` 2 enums), D
  (`folded_global_scalar_type`), E (`_pmm_reset_contiguous_registry`) — unchanged,
  still need an owner decision, as filed above.

---

## Round 3 — 2026-09-01, suite4 census re-baselined against `origin/main` `c0cae452481`

Evidence base: `/tmp/suite4.log` (started 2026-08-31 13:43, binary from
`4b4e2a304b4`), 362 distinct symbols. **29 commits landed on `main` after the
log started**, so a log row proves a failure at 13:43, not today. Every symbol
below was re-checked against a seed built from `c0cae452481` in a private
worktree, discriminated by `bin/simple compile <probe>.spl` with the exit
status read into a variable on the next line — never through a pipe.

### Stale vs live split (top clusters, 655 of 1266 rows)

| symbol | rows | verdict on `c0cae452481` |
|---|---|---|
| `_pmm_reset_contiguous_registry` | 215 | LIVE, cause E — **fixed here** |
| `folded_global_scalar_type` | 110 | LIVE, cause D — **fixed here** |
| `value` | 76 | STALE — `std.nogc_sync_mut.js.engine.runtime` probes clean (PR #182) |
| `rt_random_randint` | 69 | LIVE, cause B — **fixed here** |
| `print_raw` | 68 | STALE at the filed site — `std.nogc_sync_mut.lsp.lsp_protocol` probes clean |
| `_inc32` | 24 | STALE — defined `src/os/crypto/aes256_gcm.spl:559` since `d7a13a45f6b` |
| `manifest_reason_content_hash_mismatch` | 22 | LIVE, cause E — **fixed here** |
| `exec_memory_allocs_remove` | 14 | LIVE, cause E — **fixed here** |

### Cause E resolved: it was a bad merge, not "never written"

The doc's open question ("dropped by a bad merge or never written?") is
answered. `git show 856847ef887:src/os/kernel/memory/pmm.spl` contains
`_pmm_reset_contiguous_registry` **and** `pmm_is_live_contiguous_allocation`;
both are absent from `a8244005f9b` and `e274cd33719`, the two
`chore: merge all share-history worktree branches into main` commits. So the
symbols were real, working code that a merge dropped while leaving every call
site behind — including `memory_leveling_manager.spl:30`, which still
`use`s `pmm_is_live_contiguous_allocation` from a module that no longer
defines it.

The restore is **surgical, not a file rollback**: `pmm.spl` at `main` is AHEAD
of `856847ef887` on refcounts (fixed `[u16; MAX_PHYS_PAGES]` array, the O(n^2)
`.push()` fix) and BEHIND only on the contiguous registry. Both directions were
diffed before choosing. Restored: the two registry arrays, the five
`_pmm_*_contiguous*` helpers, the `_pmm_remove_containing_page` call in
`pmm_free_page`, the `_pmm_record_contiguous` rollback path in
`pmm_alloc_pages`, and the public `pmm_free_page_range` /
`pmm_is_live_contiguous_allocation`.

**Layering, again.** Fixing it exposed `_pmm_alloc_page_address`, which appears
nowhere in the suite4 census. The same merge had renamed that function's header
to a *second* `pmm_alloc_page() -> PageFrame?` while leaving its `0` terminator
and its caller — a duplicate definition (live cause C) plus a missing symbol in
one edit. Reconstructed from `ae55a746719`, which carries the original verbatim.

### Sites fixed

| site | symbol | cause | fix |
|---|---|---|---|
| `src/os/kernel/memory/pmm.spl` | `_pmm_reset_contiguous_registry`, `pmm_is_live_contiguous_allocation`, `_pmm_alloc_page_address` | E (merge-dropped) | restore the registry block + call sites; re-identify `_pmm_alloc_page_address` |
| `src/os/kernel/loader/artifact_manifest.spl` | `manifest_reason_content_hash_mismatch` | E | add the missing family member; the literal and semantics are fully specified by `manifest_verify_content_hash`'s own docstring, and `artifact_manifest_spec.spl:67` already imports it |
| `src/compiler/99.loader/loader/smf_mmap_native.spl:276,383` | `exec_memory_allocs_remove` / `_len` | E | the helpers never existed; `EXEC_MEMORY_ALLOCS` is a module-level `Dict<i64,i64>` in the same file, already used directly at `:249` and `:376`. Calls replaced with `.remove(address)` / `.len()` (Dict.remove verified by probe) |
| `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` | `folded_global_scalar_type` | D | hoisted the class-scope plain `fn` to module level — it takes no `self`, so behaviour-identical. **The resolver question stays open**: this is a recorded workaround, not an answer to whether a class-scope associated function should be visible to sibling `me` methods |
| `src/app/office/sheets/formula.spl:6607,6614,8402` | `rt_random_randint` | B | `rt_random_randint` IS backed (`compiler_rust/runtime/src/value/sffi/random.rs:68`), so this is a resolution bug, not an unbacked extern. Fixed by importing the existing wrapper `std.sffi.math.{random_randint}` — deliberately NOT by adding a 4th `extern fn` declaration, which would feed cause C |

### Before/after, same seed built from `c0cae452481`

```
before: rc=1 os.kernel.memory.pmm        :: undefined identifier: _pmm_reset_contiguous_registry
after:  rc=0                                                                    <- fully clean
before: rc=1 artifact_manifest           :: undefined identifier: manifest_reason_content_hash_mismatch
after:  rc=1 artifact_manifest           :: [requires the interpreter]          <- pre-existing
before: rc=1 smf_mmap_native             :: undefined identifier: exec_memory_allocs_remove
after:  rc=1 smf_mmap_native             :: [requires the interpreter]          <- pre-existing
before: rc=1 mir _MirLowering            :: undefined identifier: folded_global_scalar_type
after:  rc=1 mir _MirLowering            :: undefined identifier: hir_ty         <- LAYERED, new, not in the census
before: rc=1 app.office.sheets.formula   :: undefined identifier: rt_random_randint
after:  rc=1 app.office.sheets.formula   :: [requires the interpreter]          <- pre-existing
```

Tests: `pmm_spec` 25/25 (3 new registry scenarios added — they do not compile
before the fix), `artifact_manifest_spec` 31/31,
`app/office/sheets/cell_format_spec` 18/18.
`compiler/mir/array_at_native_lowering_spec` is 4/10 both with and without the
hoist — pre-existing, measured on a reverted copy of the same file, not a
regression from this change.

### Still open

- `hir_ty` — newly exposed by the cause-D fix, owner unknown.
- `print_raw` (68) — the filed lsp_protocol site probes clean, but the cause-C
  signature collision across 10 sites is untouched and remains a decision.
- `_append_bytes` (9), `Platform` (9), `_u8_at` (4), `alloc` (1) — cause C,
  unchanged.
- The remaining ~350 long-tail symbols are unre-baselined; every one of them
  needs the stale-vs-live check above before it is worked.

### Round-3 verification addenda (measured, not inferred)

- **Mutation-red on the 3 new `pmm_spec` scenarios.** With `pmm.spl` reverted to
  `c0cae452481` and the spec unchanged: `25 total, 22 passed, 3 failed` — exactly
  the three new scenarios, and only those. Restored: `25/25`. The earlier
  "do not compile before the fix" wording was an inference; this is the run.
- **Downstream importer.** `use os.kernel.memory.memory_leveling_manager.*`
  compiles **rc=0, fully clean** after the restore. That module's `use` of
  `pmm_is_live_contiguous_allocation` (`:30`) had been dangling since the merge,
  so this is the strongest confirmation that the restored surface is the one its
  real caller expects — not just that pmm's own closure resolves.
- **Scope of proof, restated so it is not misquoted.** "430 rows" is the count
  *attributed to these five symbols in the suite4 log*. Per round 1's retraction,
  the mapping from a fixed module to a wrapper count is still NOT established —
  no failing wrapper was captured here either. Read it as attribution, never as
  a measured effect of this change.
