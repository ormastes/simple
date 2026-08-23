# Dual-implementation test sharing assessment (2026-08-23)

Measured at `origin/main` `20f4ed3de0c` in a clean worktree (`/mnt/fast/wt-dualimpl-1`).
Every number below was produced by a command in this session; anything not measured is
labelled ESTIMATE.

## Headline

The framing of the question ("could the pure-Simple specs be run against the Rust
implementation via SFFI") is inverted by the evidence. **The 21,208 `*_spec.spl` files
already run on the Rust implementation, and only on it.** `bin/simple` is the Rust seed —
it says so itself:

```
$ bin/simple --version
WARNING: this Rust-built Simple binary is a bootstrap seed only; ...
```

`bin/simple test` spawns `bin/simple run <spec>` per file
(`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:415` `build_child_args`,
args `["run", file_path]`) with `SIMPLE_EXECUTION_MODE=interpret` forced
(`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:111`). So the spec suite is
executed by the Rust seed's tree-walk interpreter today. What does **not** run the suite is
the pure-Simple compiler and the Rust seed's own JIT/native backends. SFFI is not the
missing mechanism, and no marshalling layer is required.

## Q1 — Shared architecture?

Both trees are phase-parallel at directory granularity. Measured LOC:

| phase | pure-Simple (`src/compiler/`) | Rust seed (`src/compiler_rust/`) |
|---|---|---|
| lex/parse | `10.frontend` 66,046 | `parser` crate 52,290 |
| blocks | `15.blocks` 5,430 | `compiler/src/blocks` 8,802 |
| HIR | `20.hir` 28,702 | `compiler/src/hir` 35,471 (+ `hir-core` 1,390) |
| traits | `25.traits` 2,211 | `compiler/src/trait_coherence.rs` (single file) |
| types | `30.types` 18,928 | `type` crate 10,564 + `compiler/src/type_check` 208 |
| semantics | `35.semantics` 37,186 | `compiler/src/semantics` 1,073 |
| mono | `40.mono` 10,863 | `compiler/src/monomorphize` 6,460 |
| MIR | `50.mir` 44,723 | `compiler/src/mir` 27,456 |
| borrow | `55.borrow` 3,396 | **no counterpart** (no `*borrow*` dir in the seed) |
| mir opt | `60.mir_opt` 26,450 | `compiler/src/optimizations` 237 |
| codegen | `70.backend` 113,699 | `compiler/src/codegen` 72,621 |
| link | (in `70.backend`) | `compiler/src/linker` 10,163 |
| driver | `80.driver` 32,028 | `driver` crate 79,858 + `compiler/src/pipeline` 37,817 |
| mdsoc | `85.mdsoc` 7,357 | **no counterpart** |
| interp | `95.interp` 5,196 | `interpreter*` ≈ 92,000 (11 dirs/files) |
| loader | `99.loader` 14,191 | `loader` 11,655 + `native_loader` 1,462 |

So: **the seed does have HIR and MIR** — it is not AST→MIR. Both go
parse → HIR → types → mono → MIR → codegen → link. Genuine divergences:

1. **Borrow checking and MDSOC exist only in pure-Simple.** No `borrow`/`mdsoc`
   directory exists anywhere in the seed (measured by `find -type d`).
2. **MIR optimisation is essentially absent in the seed** (237 LOC vs 26,450).
3. **The weight is inverted between interpreter and everything else.** The seed's
   interpreter family is ~92k LOC — larger than its codegen — while pure-Simple's
   `95.interp` is 5,196 LOC. The seed is primarily an *interpreter* that also has a
   compiler; the pure-Simple tree is a *compiler* that also has an interpreter.
4. `semantics` is 37,186 vs 1,073 — the seed folds most semantic work into HIR lowering
   and the interpreter rather than a distinct phase.

Confirmed twin pairs remain real (seed `parser_impl/core.rs` vs the pure-Simple parser; C
runtime vs Rust runtime, same `waitpid` EINTR bug in `ce3c2bf6c71`), but the correspondence
is *phase-level*, not data-model-level: no shared IR schema, no shared serialisation.

## Q2 — Can the specs run against the Rust impl?

They already do (see Headline). The real question is therefore: **can the specs run on any
engine other than the seed's tree-walk interpreter?** Measured answer: no, and the blocker
is structural, not harness plumbing.

**Refuted premise 1 — "`TestExecutionMode` has no JIT variant."** There are *two* distinct
enums with that name. `src/lib/nogc_sync_mut/test_runner/execution_strategy.spl:14` is an
*isolation* enum (Native/Process/Safe/Container/ContainerSequential). The engine enum is
`src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:11`:
`Interpreter | Smf | Native | Compile | Composite(spec)`. `--mode jit` is parsed
(`test_runner_args.spl:61-62` → `Composite("jit")`), dispatched
(`src/app/test_runner_new/test_runner_main.spl:780`), and routed
(`test_executor_composite.spl:46` → `run_test_file_jit`). A JIT lane exists and is wired.

**The actual blocker — BDD verbs are Rust interpreter intrinsics.** `describe`/`it`/
`expect` are implemented as native intrinsics in
`src/compiler_rust/compiler/src/interpreter_call/bdd.rs:619`, tracking pass/fail counts in a
Rust thread-local. The runner's own comment states this and states the consequence
(`test_runner_execute.spl:107-138`): a `run <file>` child "must execute in interpreter mode
to load BDD test intrinsics ... Without this, `simple test --mode=interpreter` can still
dispatch a child in compile mode, producing parse errors + zero evidence." A pure-Simple
`describe` does exist (`src/lib/nogc_sync_mut/spec.spl:81`) but is shadowed by the
intrinsic, and its module-level counters are dead code in interpreter mode. HIR lowering
does have a `"describe"` arm (`compiler/src/hir/lower/stmt_lowering.rs:2815`), so the
compiled path is started but not finished.

**Empirical check (measured, one spec, 220 lines, 39 examples):**

| invocation | result |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpret bin/simple run <spec>` | `39 examples, 0 failures`, rc=0 |
| `SIMPLE_EXECUTION_MODE=jit bin/simple run <spec>` | `39 examples, 0 failures`, rc=0 |
| `bin/simple test <spec> --mode=interpreter` | runs (gc-warnings only) |
| `bin/simple test <spec> --mode=native` | **fails to compile**: `error[E1002]: function 'fun' not found`, plus export-form errors |

Caveat, stated rather than glossed: the two `run` rows are byte-identical, which is equally
consistent with the JIT genuinely handling this spec *and* with `SIMPLE_EXECUTION_MODE=jit`
silently degrading to the interpreter — `src/app/io/jit_ffi.spl:283` logs "Native JIT
unavailable: using in-process CompilerDriver", and §27 of the hardening plan records that
stage1 "runs *fully on the tree-walking interpreter*: the JIT bails at
`compiler_services.spl:168`". Distinguishing those two requires an engine receipt the run
does not currently print; **not measured**. The `--mode=native` row needs no such caveat:
it is an unambiguous hard failure.

So the ranked blockers are: (1) BDD intrinsics live only in the interpreter; (2) the native
lane cannot compile the harness at all; (3) only then the 18 divergent builtins.

## Q3 — Effort

Split as requested.

(a) **Make the runner able to target a non-interpreter engine.** Mostly already done. The
enum variant, the arg parsing, the dispatch and the composite router all exist. What is
missing is a *verifiable engine receipt* (so a run cannot silently degrade) and removal of
the unconditional `env_set("SIMPLE_EXECUTION_MODE", "interpret")` at
`test_runner_execute.spl:111`. ESTIMATE: small — 2-4 files, days not weeks. Low risk,
because it changes only which child is spawned.

(b) **Make the specs pass there.** This is the whole cost and it is not harness work:
  1. Port `describe`/`it`/`expect`/matchers off the Rust thread-local intrinsic onto a
     representation the compiled path can emit — i.e. finish
     `hir/lower/stmt_lowering.rs:2815` and make `src/lib/nogc_sync_mut/spec.spl` the single
     implementation. Touching `interpreter_call/bdd.rs`, `hir/lower/stmt_lowering.rs`,
     `codegen`, and `spec.spl`. High risk: it changes how every one of 21,208 specs reports.
  2. Fix whatever makes `--mode=native` fail before it reaches any spec (E1002 `fun`).
  3. The 18 divergent builtins across 711 affected specs
     (`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`).

**Plain answer:** the blocker is *not* the harness, and it is not only the 18 divergent
builtins either. It is that the assertion vocabulary itself is a Rust interpreter intrinsic.
The builtins are the second-order problem; you cannot even reach them until the BDD verbs
compile. ESTIMATE (unmeasurable cheaply): (a) days; (b) step 1 alone is a multi-week lane
with suite-wide blast radius.

## Q4 — Rust test coverage

**The headline count is mostly vendored.** Measured:

| metric | all | owned (excl. `vendor/`) |
|---|---|---|
| `.rs` files | 30,045 | **1,714** |
| `#[test]` attributes | 45,488 | **10,246** |
| files matching `*test*` | 1,513 | 257 |

So 35,242 of the 45,488 (77%) belong to third-party crates and are out of scope per
CLAUDE.md's Owned-Code Scope. Per owned crate:

| crate | files | LOC | `#[test]` | tests/kLOC |
|---|---|---|---|---|
| compiler | 771 | 389,054 | 4,233 | 10.9 |
| runtime | 355 | 138,181 | 1,645 | 11.9 |
| driver | 211 | 79,858 | 1,547 | 19.4 |
| parser | 146 | 52,290 | 882 | 16.9 |
| test | 34 | 11,754 | 923 | 78.5 |
| type | 27 | 10,564 | 308 | 29.2 |
| loader | 38 | 11,655 | 134 | 11.5 |
| common | 36 | 10,515 | 118 | 11.2 |
| sdn | 15 | 4,488 | 99 | 22.1 |
| util | 23 | 6,416 | 89 | 13.9 |
| dependency_tracker | 6 | 2,161 | 56 | 25.9 |
| gpu | 13 | 4,428 | 50 | 11.3 |
| wasm-runtime | 8 | 2,420 | 43 | 17.8 |
| simd | 9 | 3,441 | 44 | 12.8 |
| native_loader | 10 | 1,462 | 32 | 21.9 |
| native_all | 2 | 1,972 | 12 | 6.1 |
| hir-core | 1 | 1,390 | **0** | 0 |
| runtime_abi | 1 | 60 | 0 | 0 |
| compiler_backfill | 2 | 17 | 0 | 0 |

Within the `compiler` crate the distribution is the finding, and it is **inverted relative
to what actually executes the spec suite**:

| module | LOC | `#[test]` | tests/kLOC |
|---|---|---|---|
| codegen | 72,621 | 739 | 10.2 |
| mir | 27,456 | 527 | 19.2 |
| pipeline | 37,817 | 389 | 10.3 |
| hir | 35,471 | 330 | 9.3 |
| interpreter_extern | 52,306 | 286 | 5.5 |
| blocks | 8,802 | 201 | 22.8 |
| linker | 10,163 | 145 | 14.3 |
| lint | 7,370 | 123 | 16.7 |
| **interpreter** | 12,973 | **34** | **2.6** |
| **interpreter_call** | 10,862 | **29** | **2.7** |
| **interpreter_method** | 7,136 | **21** | **2.9** |
| **interpreter_helpers** | 4,190 | **16** | **3.8** |
| monomorphize | 6,460 | 40 | 6.2 |
| macro | 2,266 | 3 | 1.3 |
| concurrent_providers | 2,033 | **0** | 0 |
| type_check | 208 | 0 | 0 |
| optimizations | 237 | 0 | 0 |

The interpreter family — ~92k LOC, the engine that runs all 21,208 specs and the whole
stage1 bootstrap — sits at 2.6-3.8 tests per kLOC, the thinnest coverage in the crate, while
codegen and MIR (which the spec suite never exercises) are 3-7x denser. `concurrent_providers`
(2,033 LOC) has zero.

**Unit vs pipeline:** 1,011 owned files contain at least one `#[test]`, i.e. the tests are
overwhelmingly *inline unit tests* colocated with implementation. Eleven crates additionally
carry a cargo integration-test directory (`compiler/tests`, `runtime/tests`, `parser/tests`,
`driver/tests`, `type/tests`, `loader/tests`, `native_loader/tests`, `common/tests`,
`sdn/tests`, `lib/tests`, `wasm-runtime/tests`), and the dedicated `test` crate (34 files,
923 tests, 78.5/kLOC) is the one place tests dominate — that is where real-pipeline exercise
lives. ESTIMATE: the great majority of the 10,246 are unit-level.

**Coverage tooling: none, in owned code.** Every `llvm-cov`/`tarpaulin`/`grcov` hit in the
tree is under `src/compiler_rust/vendor/`. There is no owned coverage script under
`scripts/` and no coverage profile in an owned `Cargo.toml`. **Line/branch coverage is
therefore unmeasured and cannot be reported here.** `#[test]` density is a proxy, not
coverage, and is presented as such. `compiler/src/coverage.rs` and `spec_coverage.rs` exist
but serve *Simple-program* coverage, not Rust self-coverage.

## Ranked list — what would make sharing feasible

1. **Make the BDD verbs implementation-neutral.** One `.spl` implementation of
   `describe`/`it`/`expect` that both engines execute, replacing the Rust thread-local
   intrinsic. Everything else is downstream of this.
2. **Print an engine receipt on every run.** Until a run states which engine executed it,
   no A/B result between engines is trustworthy — the `SIMPLE_NO_JIT` precedent in
   `args_and_os_commands.spl:350-353` is exactly this failure ("A/B runs done with it
   silently compared JIT against JIT").
3. **Fix `--mode=native` compiling the harness** (E1002 `fun` not found).
4. **Close the 18 divergent builtins**, then re-run the 711 affected specs.
5. **Add coverage tooling** (`cargo llvm-cov`) so Q4 can be answered with real numbers.
6. **Cover the interpreter family**, the least-tested and most-executed code in the seed.

## Recommendation

Do **not** build an SFFI bridge. There is nothing for it to bridge: the specs already
execute on the Rust seed, and the pure-Simple compiler is the side that cannot run them.
The valuable, tractable work is (1) and (2) above — a neutral BDD vocabulary plus a
non-forgeable engine receipt — which together turn the existing `--mode` matrix into a real
differential-testing harness across interpreter / JIT / native / pure-Simple. That is a
cheap harness change gated behind one hard semantic change, and it is the only route by
which the 21,208 specs become evidence about more than one engine.

Second recommendation: correct the "45,488 `#[test]`" figure wherever it is quoted. The
owned number is 10,246, and none of it is coverage-measured.
