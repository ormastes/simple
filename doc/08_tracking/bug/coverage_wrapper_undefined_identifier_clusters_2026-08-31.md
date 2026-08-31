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

Two independent facts confirm the retraction:

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
2. Run-state not replicated: the suite3 run's `SIMPLE_MCDC_MODE` value, its
   concurrency, its cwd, or its `TMPDIR` contents.
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
