# Bug: Stage 4 `--low-memory` build grows past 25 GB RSS

## Status

Source plumbing fixed; executable acceptance remains open. The bounded
incremental Stage 4 build was stopped deliberately before host/session failure;
no Stage 4 artifact was produced, so the canonical essential
test/lint/duplication gate remains pending.

The canonical wrapper passed `--low-memory`, but the Stage4 branch bypasses the
ordinary argument parser and rebuilt `CompileOptions` through the fixed-arity
pure-Simple API. That API left `low_memory` at its default `false`, disabling
all existing source/AST/HIR/MIR eviction points. Its sole source caller is the
canonical Stage4 branch, so the fixed-arity owner now enables low-memory mode
directly. The source regression pins the option; bounded RSS and artifact
evidence are still required.

The next active retention owner was `ast_reset()`: every parsed file replaced
the declaration, expression, statement, match-arm, module, and lexer-state
arrays with fresh allocations. The core runtime keeps registered arrays for
the process lifetime, so those resets both retained old buffers and lengthened
later validity scans. All three arena reset owners now allocate only nil module
arrays, clear reusable outer storage in place, and reset one-element state slots
without replacing them. The same fix adds the trait/mutability and GPU pools
that the old reset accidentally omitted. Existing sequential large-then-small
parse coverage remains the stale-state oracle, and a source contract rejects
unconditional arena replacement. A cached current-source compile emitted the
changed compiler objects; final linking stopped on the separately known
`nogc_async_mut__path__join` provider gap, so no RSS or executable PASS is
claimed.

Parser initialization now follows the same ownership rule: it clears the
current-parse diagnostics and struct-name lists, overwrites token/cache
singletons, and reuses the lexer's outer active-lexer slot. The source-specific
`CoreLexer` payload is still replaced. Pure runtime `source.chars()` now caches
each one-byte character handle within a conversion, retaining at most 256
distinct one-byte string objects plus unchanged multibyte objects. The O(N)
outer character-reference array and Stage4 RSS acceptance remain open.

### 2026-07-19 bounded follow-up

A current-source, cache-preserving self-host refresh compiled past the cached
frontend objects but hit its single 180-second cap before linking an artifact;
it was not retried. A smaller `Lexer.new` RSS probe emitted an archive with one
compile and 20 cache hits, but the preserved Stage3 executable wrapper could
not select the supplied pure-Simple runtime archive. Its `core-c-bootstrap`
fallback selected an incomplete archive and stopped on missing
`rt_heap_registry_count`; direct archive linking exposed the same incomplete
owner projection. No RSS baseline is claimed from these failed link paths.

Source review also rules out freeing `previous.source_chars` before replacing
the active lexer slot: `CoreLexer` copies array fields shallowly, so that order
creates a use-after-free window. The attempted lifecycle constructed the fresh
lexer, captured the whole retired lexer, replaced the slot, and only then
shallow-released `retired_core_lexer.source_chars`.

### 2026-07-24 correction

Fresh CI disproved the initial eager-release diagnosis: removing only
`rt_array_free` left the identical first-file-good/second-file-corrupt failure.
The next isolated candidate is the preceding optimization that overwrote the
large `CoreLexer` struct through `current_core_lexer_slot[0]`. The lexer now
restores pre-optimization whole-owner replacement, and the two-parse regression
rejects both element overwrite and eager release. This is not promoted as the
root cause until exact Stage4 CI passes. Full artifact and RSS acceptance
remain open.

## Reproduction

Use the constructor-preserving Stage 3 compiler to build only the full CLI with
`--runtime-bundle core-c-bootstrap`, `--entry-closure`, `--low-memory`, two
threads, and the existing native cache. The exact invocation is the
`bootstrap_native_build_main` command in
`scripts/bootstrap/bootstrap-from-scratch.sh`; this run did not invoke the full
bootstrap pipeline.

Observed on 2026-07-18:

- one `simple native-build` process remained CPU-active (about 100% CPU), so it
  was not classified as a deadlock;
- elapsed time exceeded 10 minutes without an output artifact or progress
  marker;
- RSS reached 24,916,288 KiB (about 23.8 GiB) despite `--low-memory`;
- the process was interrupted once with exit 130 under the runaway/budget
  guard; it was not retried.

### 2026-07-28 bounded incremental follow-up

A current-source pure-Simple Stage3 compiler was rebuilt incrementally on base
`958db10638d`: 45 compiled, 647 cached, zero failed, 194.9 seconds, binary
SHA-256 `a920123d919c4a4c384161e16fe35a1853d6e3da6bfd3a4a4e7291a2c072f04d`.
The full-CLI cycle used that binary, `--low-memory`, two threads, the retained
cache, and phase profiling. Source loading found 1,340 unique files. A local
symbol-retention repair stopped caching imported/package-sibling symbols in
every module; observed RSS was about 7.0 GiB at 15m38s, versus about 21.7 GiB
in the preceding unfiltered run at 21m32s.

The run still could not converge: only 50 HIR modules completed by 15m38s.
Large directory packages repeatedly spend minutes in
`resolve_package_sibling_symbols`, which scans every `modules_by_name` key and
registers every direct sibling's symbols for each module. The process was
stopped at the third-cycle cap with no ELF. Retained log:
`build/native_probe/rebased-stage4-cycle3-final.log`, SHA-256
`92efd6d06e9c5e27ad45e98f472a953873bc78943bed43e2cb3e5855f2656fea`.
The next fix must replace repeated eager package-wide registration with an
indexed or lazy sibling resolver and retain equivalent bare cross-file name
semantics. No further build is permitted in this verification window.

### 2026-07-28 lazy sibling resolution repair

`resolve_package_sibling_symbols` now retains only direct sibling module keys.
Ordinary expression, named-type, pattern, async-type, and impl-owner lookup
registers one requested sibling symbol on the first miss, at module scope, and
caches genuine misses. The existing `register_imported_symbol` path remains the
single owner of visibility, re-export, callable-signature, type-method, enum,
and trait-default semantics. A focused unit regression requires bare sibling
function/type resolution while proving an unused sibling declaration is not
registered; a three-file disk fixture covers the equivalent native package.

One pure-Simple incremental compiler build accepted the source (693 compiled,
zero failed, 647.3 seconds), producing
`build/native_probe/lazy-sibling-stage3-cycle1/simple`, SHA-256
`16f89715874448595f91a6a39043222c1967e320e9b73a9d519e61db4ab2c4c4`.
That artifact linked 43 unresolved compatibility stubs and crashed when used
as a second-generation native-build producer, so it is not admitted runtime
evidence. The retained full-Stage4 three-cycle cap still forbids another broad
build in this verification window; elapsed/RSS and essential-tools acceptance
remain open.

## Required fix and regression

1. Add bounded phase/progress reporting to the pure-Simple native-build driver
   so compilation, aggregation, and linking can be distinguished without a
   debugger.
2. Profile retained module/MIR/object state in the Stage 4 entry-closure path
   and release completed-module state under `--low-memory`.
3. Add an isolated Stage 4 resource smoke that samples max RSS and fails on
   timeout or an agreed memory ceiling before the essential-tools gate.
4. After the resource smoke passes, run
   `scripts/check/check-bootstrap-essential-tools-smoke.shs` exactly once with
   the resulting Stage 4 binary.

Acceptance requires a produced full CLI, bounded warm elapsed time/RSS evidence,
and green test-runner, lint, and duplication probes. A CPU-active process with
unbounded RSS is not a passing “slow build.”

### 2026-07-28 current-overlay incremental producer

The fresh window bound the exact overlay at HEAD `24a77be3c89a`, tracked
`src scripts test` diff SHA-256
`c5233e73b817e1ca915aa768f62856200b7fc43b542b2715d03ed7c5eab218b1`,
pure-Simple parent SHA-256
`a920123d919c4a4c384161e16fe35a1853d6e3da6bfd3a4a4e7291a2c072f04d`,
and core-C runtime SHA-256
`822f4ef4f1f6cad0d3e3a8a0a51c0f68de8bf23452059ec5d3c292a9a9750605`.
All runs used the retained exclusive cache, two threads, `--low-memory`, the
full `src/app/cli/main.spl` entry closure, and a 32 GiB cgroup cap.

Cycle 1 intentionally retained phase profiling and reproduced the old parent's
per-expression log/RSS cost; it was stopped after 1,300.86 seconds at
24,951,108 KiB max RSS. Cycle 2 disabled profiling and enabled
`SIMPLE_NATIVE_INCREMENTAL=1`; unrelated host jobs drove available RAM below
10%, so `earlyoom` terminated it after 594.71 seconds at 10,623,772 KiB rather
than a compiler failure. Cycle 3 ran after resource admission, completed HIR
finalization with no HIR error, then its cgroup OOM-killed `simple` at
33,483,972 KiB anonymous RSS before codegen/link. No executable was produced.
Retained log SHA-256 values are respectively
`a2bc96cbec9a304a94bb8d8b926996f598c2cb1f185a2ef50566b061d7156760`,
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`,
and `5cc177b2746cf4a117df4917cb9dde2ec3f0a30740e7a7157befb59e23967cc5`.

The remaining root cause is retained HIR/module state exceeding the low-memory
ceiling before codegen. The next implementation cycle must release completed
module state or otherwise bound its owner lifetime; raising the cap is not the
fix. The three-cycle guard forbids another producer in this window.

### 2026-07-28 dead Stage 4 flat-store repair

The retained owner is now narrower. Every Stage 4 module populated canonical
`CompileContext.hir_modules` and also materialized legacy
`_bootstrap_hir_functions` plus `_bootstrap_hir_module_*` copies. Stage 4 never
consumes those globals: both flat-HIR-to-MIR dispatches require
`SIMPLE_BOOTSTRAP_STAGE4 != 1`; the Stage 4 path reads only canonical HIR.
Normal MIR lowering likewise stored each function in its returned `MirModule`
and in the unused `_bootstrap_mir_functions` accumulator.

Current source adds a constructor-hoisted `bootstrap_flat_store` predicate and
suppresses all legacy flat HIR reset/add/materialization when Stage 4 is active.
It also suppresses the analogous duplicate MIR function accumulator while
preserving canonical HIR/MIR and cross-module return-type registration. This
avoids allocation rather than attempting unsafe post-hoc deep frees: runtime
values are pointer-aliased, and the portable deep-free surface cannot prove
external ownership.

`SIMPLE_COMPILER_MEMORY_PROFILE=1` now enables coarse per-phase/per-module
elapsed plus `heap_registry` receipts without enabling expression/function
trace traffic. The focused HIR spec passed 4/4 under bounded seed diagnostics;
working and staged direct-runtime guards pass. Pure-Simple runtime measurement
remains pending because the three-cycle producer window is exhausted, so no
RSS improvement or completion claim is made yet.

The next authorized producer window should run exactly once with the retained
incremental cache and the coarse profiler (the canonical CLI entry is
`src/app/cli/main.spl`):

```bash
RUNTIME_ROOT=/home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap
mkdir -p build/native_probe/current-overlay-full-cli-next
flock -n build/bootstrap/native_cache/.stage4-producer.lock \
  sh scripts/resource/run_capped.shs timeout -k 30s 3600s \
  env RUST_LOG=error SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1 \
  SIMPLE_BOOTSTRAP_LOW_MEMORY=1 SIMPLE_NATIVE_INCREMENTAL=1 \
  SIMPLE_COMPILER_MEMORY_PROFILE=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NATIVE_BUILD_THREADS=2 \
  SIMPLE_NATIVE_BUILD_CACHE_DIR=build/bootstrap/native_cache \
  SIMPLE_RUNTIME_PATH="$RUNTIME_ROOT" \
  SIMPLE_BINARY="$PWD/build/native_probe/rebased-latest-stage3-cycle1/simple" \
  build/native_probe/rebased-latest-stage3-cycle1/simple native-build \
  --target x86_64-unknown-linux-gnu --backend cranelift \
  --runtime-bundle core-c-bootstrap --source src/compiler --source src/app \
  --source src/lib --source examples/10_tooling --entry-closure --low-memory \
  --threads 2 --cache-dir build/bootstrap/native_cache --mode one-binary \
  --entry src/app/cli/main.spl \
  --runtime-path "$RUNTIME_ROOT" \
  -o build/native_probe/current-overlay-full-cli-next/simple \
  >build/native_probe/current-overlay-full-cli-next/producer.log 2>&1
```

Before launch, bind the source, parent, runtime, literal command, cache, and lock
identities in the output directory. Afterward record exit status and capped
resource receipt; admit a successful output only with its SHA-256 and the
incremental reused/rebuilt counts from the producer log.

## Current-parent prerequisite result (2026-07-28)

The command above cannot exercise a compiler-source memory fix when its parent
predates that fix: the parent performs HIR/MIR lowering while compiling the new
source. A current Stage 3 parent must therefore be produced first with the
canonical positional `src/app/cli/bootstrap_main.spl` route (no `--entry`,
`--entry-closure`, or `--source`), then used for Stage 4.

The authorized three-cycle window produced no executable:

- cycle 1 was stopped at 12.92 GiB after unrelated builds crossed the declared
  host-headroom floor; the cache was preserved;
- cycle 2 proved the old parent still followed the prior slope and was stopped
  after 1,197 seconds at 26.98 GiB maximum RSS;
- cycle 3 used the corrected positional Stage 3 route and was cgroup OOM-killed
  after 1,409 seconds. The last observed cgroup peak was 31.16 GiB under the
  32 GiB cap; the systemd journal records `Failed with result 'oom-kill'`.

Cycle receipts are under `build/native_probe/current-overlay-full-cli-next*`
and `build/native_probe/current-source-stage3-cycle3/`. A future bounded window
must first produce the current Stage 3 parent; direct Stage 4 from the retained
old parent cannot validate or benefit from this repair.
