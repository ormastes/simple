# Coverage-wrapper `Undefined("undefined identifier: X")` — root-cause grouping

Date: 2026-08-31
Status: PARTIALLY FIXED (cause B fixed at 5 sites; causes A, C, D, E filed here)
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

## Cause A — stale deployed seed (NOT a live bug)

The `simple` binary used for the suite3 run is dated **2026-08-26**. The
`panic` builtin was registered in the seed typechecker by **777f3c99583**
(2026-08-30), whose own comment names this exact symptom. On that stale binary
even a root-module `panic("x")` fails; on a seed built from `origin/main`
(b0be388ec46) it compiles.

Action: **redeploy the seed.** No source change is warranted. Any future
triage of this log must use a freshly built binary as the discriminator.

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
| `use lib.sdn` | clean (no `Undefined`) | `String` (8) / `Dict` (6) / `value` (6) do **not** come from `src/lib/sdn/__init__.spl`'s unqualified `case String(s)` / `case Dict(entries)` patterns, which was the leading hypothesis. Most likely cause A. |
| `use std.nogc_sync_mut.package.dist` | clean | `Platform` not reproduced from this side |
| `use compiler.backend.linker.smf_enums` | clean | `Platform` not reproduced from this side either |
| `use std.nogc_sync_mut.composition.codec` | clean | — |
| `use std.nogc_sync_mut.compression.gzip.compress` | `Undefined("undefined identifier: gzip_stream_compress")` | live cause B — **now fixed** |

Still unclassified: `String` (8), `Dict` (6), `value` (6), `NativeTensor`, `Node`,
`fs`, `temp_dir`, `float`, `raise`, `alloc`, `shared_examples`, `context_def`,
`async_mode`, `mul_scalar`, `_b64_index`. Full (symbol, spec) map extracted from
suite3 is reproducible with:

```
grep -oE 'spipe_wrapped__[A-Za-z0-9_]+_spec_native\.spl\): semantic: [^ ]+ Undefined\("undefined identifier: [A-Za-z_0-9]+' /tmp/suite3.log
```

These must be re-censused against a freshly built seed before any are worked:
Cause A means an unknown fraction of them are already fixed at origin.
