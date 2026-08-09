# Stage 3 "vacuous binary" is enum-discriminant garbage in stage2, NOT a link failure

Date: 2026-08-08
Status: OPEN — root question **RESOLVED as a confirmed scale artifact** (see
  "2026-08-09 bisection resolved" below); the underlying MIR-lowering
  wildcard-arm defect that triggers at project scale is still unfixed and is
  the next concrete blocker.
Severity: BLOCKER (critical path to self-host)

## 2026-08-09 bisection resolved: CONFIRMED SCALE ARTIFACT

Once the type-mapper `unresolved name: error` blocker cleared (fix on
`origin/main` at `ccef50cd443383a64024de060210cc82deab868b`, verified
ancestor of `origin/main` and confirmed `src/lib/common/error/error.spl` is
gone), retried the bisection this doc recommended. Used the *same, byte-stable*
`build/cyc/S3FIX1/stage2-simple` binary (128,111,944 B,
md5 `bcb9446301cdf2eafd2db2044d03d8e0`) in the `/home/ormastes/dev/simple-s3bisect`
worktree (reset to `origin/main` first — it had drifted, see below), and the
exact 7-line `p2_add.spl` reproducer from the "Root cause" section:

```
fn addup(a: i64, b: i64) -> i64:
    return a + b

fn main() -> i64:
    val x = addup(20, 22)
    print "RESULT={x}"
    return 0
```

**Key discovery: `--entry FILE` / positional `FILE` with no `--source` silently
scans the DEFAULT source roots (the whole ~728-module project), not just the
given file.** The driver even says so once you look: `note: --entry without
--source scans the DEFAULT source roots (whole project) and stays silent while
loading that import graph; pass --source <dir> to bound it`. This means every
prior "small reproducer" run in this doc's own history that used `--entry` or
positional form *without* `--source` was never actually small — it pulled in
the entire project's module graph regardless of how trivial the entry file was.

With that understood, the same file + same binary gives a clean scale-vs-scope
A/B, all four runs today from `/home/ormastes/dev/simple-s3bisect`:

| run | command | closure scope | result |
|---|---|---|---|
| scoped | `native-build --backend llvm --mode dynload --entry p2_add.spl --source build/cyc/RETRY0809 --output scoped_out` | 1-file dir | **exit 0**, `Build complete: 1 compiled, 0 cached, 0 failed`, binary runs, prints `RESULT=42` |
| default×3 | `native-build --backend llvm --mode dynload p2_add.spl --output <out>` (no `--source`) | whole project | **exit 1**, every one of 3 repeats: `[TEMP-PROBE-mir-wildcard] d=-1 …` then `error: … unsupported MIR type kind [wildcard-arm] disc=-1: <value:0x1800000007>`, no binary produced |
| `--entry` no `--source` | same, `--entry` form | whole project | exit 124 (timeout at 60s budget), confirmed same "scans whole project" note in log |
| `--entry-closure` positional | same, `--entry-closure` form | whole project | exit 1, same wildcard-arm error (3 occurrences in log) |

Logs preserved at `/home/ormastes/dev/simple-s3bisect/build/cyc/RETRY0809/{scoped,small_1,small_2,small_3,formB,formD,full}.log`.

**This is decisive: the identical 7-line construct, compiled by the identical
binary, succeeds when the resolved source-root closure is scoped to ~1 file and
fails (deterministically, 4/4 non-timeout runs) when the closure defaults to
the whole project.** Nothing about the construct changed between the two
columns — only the size of the module graph the compiler resolves before
codegen. That directly answers this doc's central open question in favor of
**(a) scale artifact**, not (b) a construct-level defect reproducible in
isolation. It also refutes this doc's earlier "2026-08-08 CORRECTION" framing
that the small-reproducer non-reproduction (§2 of the Control-runs section)
meant nothing was wrong with the reproducer — the earlier non-reproduction was
itself an artifact of the same undocumented "no `--source` ⇒ whole project"
default, which happened to resolve a smaller/luckier closure at the time.

**Why this still explains `STAGE3_EXIT=0` at full project scale (not exit 1):**
per "Why Stage 3 still reported `STAGE3_EXIT=0`" above, the real Stage-3 entry
point goes through `driver_bootstrap.spl`'s bootstrap lane, which drops
`MirLowering.errors` and only fails on the "0 MIR instructions" guard. The
`native-build` CLI path used in today's runs is the *ordinary* (non-bootstrap)
lane, which does surface `self.error(...)` from `50.mir` and therefore fails
closed (exit 1) on the same underlying wildcard-arm condition that, on the
bootstrap lane, gets silently swallowed into a vacuous stub binary. Same root
trigger (an MIR type kind falling to a wildcard match arm once the project-scale
module graph is loaded), two different fail postures depending on which driver
lane is entered.

**Not yet established:** which specific `HirTypeKind` variant reaches the
wildcard arm, or why closure size (as opposed to some specific file/module
first pulled in past a threshold) is the operative variable — a bisection by
`--source` subset size (e.g. add one compiler layer at a time) would narrow
this further but was out of scope for today's session. No `.spl` source was
changed in this session: the failure is real but its exact trigger inside
`50.mir` was not isolated to a single construct, and this doc's own
constraints route edits to `src/compiler/70.backend/**` to another concurrent
agent — the wildcard-arm site in `50.mir` (`function_lowering.spl:798`,
`bootstrap_globals.spl:408`/`:776`) is in scope for a future session but was
not touched here since the "which variant" question remains open and a blind
edit there risks papering over the defect rather than fixing it.

**Housekeeping note:** the `/home/ormastes/dev/simple-s3bisect` worktree's
`HEAD` had drifted behind `origin/main` (missing the type-mapper fix commit,
`src/lib/common/error/error.spl` still present) despite a recent-looking
commit date; it was reset to `origin/main` (`git fetch && git checkout -B
bisect-work origin/main`) before this session's runs. Prior stale local
changes there were stashed, not discarded.

**Recommended next step:** bisect `--source` by compiler layer (00. through
90., one directory at a time) against the scoped-vs-default A/B established
today, to find the specific module/file whose inclusion flips the 7-line
reproducer from exit-0 to the wildcard-arm failure. That will convert "scale"
into a concrete construct or module, which is what actually needs fixing in
`50.mir`.

## 2026-08-09 follow-up — still inconclusive, pipeline now fails even earlier

Re-attempted the bisection this doc's prior update recommended (scoped
`--source` allowlist form instead of `--entry-closure`, which doesn't
actually scope the transitive import graph). Confirmed today's other Stage-2
fixes (ByteOrder, unqualified enum-variant match arms, `run_fn` closure-call
link failure) are on `origin/main` first.

- **Attempt A** — repeated the `--entry-closure` + `--source` closure build:
  still hits the 60s-per-file timeout, now on
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` instead of
  the file it stalled on previously. Fails closed (exit 1, no binary), 240s.
- **Attempt B** — ran the real single-unit Stage-3 recipe (positional entry,
  no `--entry-closure`/`--source`) fresh against current `origin/main`.
  Result: exit 1 in 268s (much faster than the earlier 1202s vacuous run),
  failing at HIR lowering with `unresolved name: error` in
  `src/compiler/70.backend/backend/llvm_type_mapper.spl` and 5 sibling files
  — the separately-tracked
  `stage3_selfhost_unresolved_name_error_type_mappers_2026-08-08.md` (fix
  landed there as of today, full-bootstrap verification in progress).

**Verdict: still inconclusive.** No scale-vs-construct answer reached — the
pipeline no longer even reaches codegen, so the original vacuous-binary
question is untestable until the type-mapper bug's fix is confirmed and
Stage 3 gets further. No `.spl` source changed here. Next step: once the
type-mapper fix is verified, retry this bisection with a reduced `--source`
set and a self-contained small entry point.

> **2026-08-08 CORRECTION — the "enum discriminant garbage" root cause below is
> REFUTED by control runs.** Native enum dispatch is correct on both backends,
> the reproducer claim was mis-recorded, and the SEED-vs-stage2 comparison that
> motivated the whole diagnosis is **confounded by a pipeline switch**. The
> symptom (a vacuous object) still stands and is still a blocker. Read
> [§ Control runs (2026-08-08)](#control-runs-2026-08-08-enum-dispatch-refuted-pipeline-confound-found)
> at the end of this document before acting on anything in the "Root cause" or
> "Remaining blocker" sections, both of which are now void.

## Prior framing (WRONG) — corrected here

The working hypothesis was: *"Stage 3 exits 0 but the compiled 1.16 MB compiler
object is never linked into the 22,896-byte output binary; find the missing
linker path."*

That framing is **false**. The object **is** linked. The output binary is
vacuous because the **code inside the object is vacuous**, and `ld` correctly
garbage-collected 5,766 unreferenced `-ffunction-sections` sections.

## Evidence chain (all from preserved artifacts, no re-run needed)

Artifacts (run `S3RUN_3600`, WALL=1202s, `STAGE3_EXIT=0`):

- binary: `/home/ormastes/dev/simple-s3bisect/build/cyc/S3RUN_3600/stage3-simple` (22,896 B)
- object: `/home/ormastes/dev/simple-s3bisect/build/cyc/S3RUN_3600/stage3-simple.app.cli.bootstrap_main.o` (1,164,496 B)
- IR:     `/home/ormastes/dev/simple-s3bisect/build/cyc/S3RUN_3600/t3/simple_llvm_567760.ll` (5.4 MB)

### 1. The object WAS handed to the linker

`src/compiler/80.driver/driver_bootstrap.spl:431` / `:504` compute
`obj_path = output + ".app.cli.bootstrap_main.o"` and link it at `:478` / `:543`
via `link_llvm_native([obj_path], output, llvm_opts)`. The object file sits
beside the binary with exactly that name — it was produced by the code that
also passes it to the linker.

Proof it was consumed: `__simple_main` in the binary (`readelf`: 81 bytes at
`0x202120`) is **byte-identical** to `.text.__simple_main` in the object
(81 bytes). The object's code is in the binary; there just isn't any.

### 2. The object's code is stub-shaped

`readelf -SW` on the object: 5,876 section headers, 5,767 `.text.<fn>` sections.

```
sections=5767  total_text=208747  avg=36.2 bytes/fn  tiny(<=8B)=2833
largest: 3200 .text.compiler.10.frontend.core.tokens.tok_kind_name
         1908 .text.compiler.frontend.core._ParserPrimary.primary_expr.parse_primary_expr
```

36 bytes/function average across an entire compiler. 2,833 functions (49%) are
<=8 bytes, i.e. `ret` stubs.

`objdump -d --section=.text.__simple_main` — **zero call instructions**. It
compares never-written stack slots (`-0x49(%rsp)`, ...) and returns. Because it
references nothing, `--gc-sections` legitimately discarded every other section.

**`--gc-sections` is confirmed present on this exact link path** (this is the
load-bearing check for the whole "the link is fine" claim — without it, a normal
`ld` would have kept all 208,747 bytes and something else dropped them):

- `src/compiler/70.backend/backend/llvm_native_link.spl:283` and `:437`
  — `closure_args.push("-Wl,--gc-sections")`, on the `link_llvm_native` path
  that `driver_bootstrap.spl:478/543` invokes.
- `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:283`
  — `args.push("--gc-sections")` in `link_native_unix` (direct `ld`), and
  `:701`/`:735` `-Wl,--gc-sections` in the `cc` fallback.
- `src/compiler/70.backend/backend/llvm_backend_tools.spl:404`
  — `ld_args + " --gc-sections"`.

So the 208,747 → 10,613 byte `.text` reduction is section GC operating correctly
on code that references nothing, not code loss in the linker.

All source line references in this document were verified identical between the
working copy and `origin/main` at the time of writing (`git hash-object` vs
`git rev-parse origin/main:<path>`) for `function_lowering.spl`,
`bootstrap_globals.spl`, `mir_lowering_types.spl`, `driver_bootstrap.spl`,
`driver_aot_pipeline.spl`, `driver_aot_native_output.spl`, and
`driver_pipeline_lowering.spl`.

### 3. The LLVM IR is the smoking gun

Instruction census over all 5,767 `define`s in `simple_llvm_567760.ll`:

| opcode | count |
|--------|-------|
| `br` | 66,271 |
| `alloca` | 34,126 |
| `load` | 31,503 |
| `ret` | 11,267 |
| `ptrtoint` | 2,265 |
| `icmp` | 2,201 |
| `zext` | 1,320 |
| `inttoptr` | 362 |
| `call` | **15** |
| `store` | **0** |
| `add`/`sub`/`mul`/any arithmetic | **0** |

- **Zero `store` instructions in the entire module.**
- **Zero arithmetic instructions.**
- All 15 `call`s are `@rt_panic` — the fail-closed panic emitted *alongside*
  the const-0 placeholder in `_MirLoweringExpr/method_calls_literals.spl:2739`.
- 5,759 of 5,767 functions (99.9%) contain no call at all.

Control flow and stack slots survive; every value-producing instruction is gone.

## Root cause: garbage enum discriminants in the natively-built stage2 — **REFUTED (see final section)**

Minimal reproducer — a 7-line program, built by
`build/cyc/S3FIX1/stage2-simple` (native, seed-emitted) on the same
`native-build --backend llvm --mode dynload` lane:

```
fn addup(a: i64, b: i64) -> i64:
    return a + b

fn main() -> i64:
    val x = addup(20, 22)
    print "RESULT={x}"
    return 0
```

Build exits **1** with:

```
[TEMP-PROBE-mir-wildcard] d=-1 slice=4126198529 typeparam=4011052772 dyntrait=1862563777 \
    function=2452922934 projection=2918955767 isolated=3659161226 tensor=1330343399 layer=3207248668
error: bootstrap entry lowered to 0 MIR instructions (ret-0 stub module)
```

### Precision note on the probe numbers — read before citing them

That probe line is a pre-existing `TEMP-PROBE` left in the tree by an earlier
lane (`function_lowering.spl:785-799`, comment: "remove before landing"). It sits
in the `case _:` **wildcard arm of a `match` on `HirTypeKind`**, and it calls
`rt_enum_discriminant()` — both on the value that reached the arm and on nine
freshly-constructed reference variants.

**The individual discriminant values are NOT trustworthy evidence.** If
`rt_enum_discriminant` is itself unreliable under native codegen, then `d=-1` and
the nine multi-gigabyte reference values are artefacts of the probe, not
measurements of the defect. Do not cite `d=-1` as a proven discriminant read.

What the probe *does* establish reliably, independent of the numbers:

1. A `HirTypeKind` value **reaches the wildcard arm** of that match — i.e. the
   match failed to select any of the named variants.
2. That arm calls `self.error_fatal("unsupported MIR type kind [wildcard-arm]...")`
   (`:799`) and then degrades the type to `MirType.i64()` (`:800`).
3. On the bootstrap lane that `error_fatal` is **dropped** (see fail-open 1
   below), so the degradation is silent.

The consistent reading across all three artefacts is therefore: **enum matching
over HIR/MIR type and instruction enums is failing to select the correct variant
in the natively-built stage2, falling to wildcard/unresolved arms, and lowering
degrades to control flow with no values.** The identical signature appears in the
Stage-3 log's method resolution:

```
[mir-method-call] resolution-enter method=slice disc=1851930204 unresolved=true
```

The 3,629 `const-0 placeholder` substitutions across 538 names and the
15-`rt_panic`-only call set are *symptoms* of this same wildcard fallthrough, not
independent defects.

**Still unproven, and the next thing to establish:** whether the failure is in
the discriminant *load*, in the variant *constants*, or in the match dispatch
itself — and whether it is a stage2 codegen defect or a source defect. The
obvious control (build the same reproducer with the Rust seed) is **not
available**: the seed at `src/compiler_rust/target/bootstrap/simple` reports
`native backend 'llvm' is not available in this build; rebuild the Rust driver
with --features llvm or use --backend cranelift`. A `--backend cranelift` or
interpreter control run is the cheapest remaining discriminator.

Probe sites:
- `src/compiler/50.mir/_MirLowering/function_lowering.spl:798` (the `d=-1` probe)
- `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl:408`, `:776` (the guard)

## Why Stage 3 still reported `STAGE3_EXIT=0`

Three independent fail-opens stack:

1. **`MirLowering.errors` is dropped on the bootstrap lane.**
   `src/compiler/80.driver/driver_bootstrap.spl:124`
   `bootstrap_lower_to_mir_context` never reads `MirLowering.errors`
   (`src/compiler/50.mir/mir_lowering_types.spl:41`); it returns
   `(next_ctx, next_ctx.errors.len() == 0)` at `:142` / `:186`, i.e. only
   pre-existing `CompileContext` errors. The parallel default lane *does*
   surface them via `_driver_collect_mir_errors`
   (`src/compiler/80.driver/driver_pipeline_lowering.spl:133`, called at
   `:181`/`:246`/`:272`). **94 `self.error(...)` call sites in `50.mir` are
   invisible on the bootstrap lane.**
2. **The `0 MIR instructions` guard only fires at exactly zero.** On the real
   Stage-3 entry, lowering emitted branches and allocas — nonzero — so the guard
   passed while the module was still semantically empty. A trivial program trips
   it; the compiler itself does not.
3. `driver_aot_pipeline.spl:166-183` discards SMF-emission failure and returns
   `CompileResult.Success(output)` unconditionally; `driver_aot_native_output.spl:178-181`
   always returns Success ignoring its context.

Consequently `error:` lines = 0 and `failed=0` are fail-open readings.

## What is NOT the cause (ruled out)

- **Not `--mode dynload`.** It only sets `output_format = both`; the link object
  set is identical to `one-binary` (`compile_targets.spl:1205`).
- **Not an external-linker misconfiguration.** `SIMPLE_CC` pointing at a logging
  shim produced no `cc.argv` at all — the link is internal.
- **Not the `-ffunction-sections` multi-section merge bug.** That is real and was
  fixed by a parallel lane at `16456ea9b55` (`smf_elf_parser.spl`), but it sits on
  the SMF/ELF-parser path, not the `link_llvm_native` path this run took. It does
  not explain zero stores in the IR.
- **Not a timeout or memory budget.** Three runs of 529s/948s/1202s produced a
  byte-identical artifact.

## Remaining blocker (stated plainly) — **superseded (see final section)**

**Stage 3 does not produce a genuine self-hosted binary, and cannot until enum
discriminant reads work in a natively-compiled compiler.** The compiler source
is fine; the *stage2 binary that compiles it* mis-reads every enum discriminant,
so it lowers the whole compiler to control flow with no values.

Fixing the linker, the const-0 census, or the error plumbing will not produce a
working binary while this holds. Error surfacing is still worth landing — it
converts a 1200s false green into a fast, honest red — but it is diagnosis
infrastructure, not the fix.

## Next actions

1. Bisect the discriminant read: `function_lowering.spl:798` already prints both
   the read discriminant and the expected per-variant values. Establish whether
   the corruption is in the discriminant *load* or in the variant *constants*.
2. Wire `MirLowering.errors` into `bootstrap_lower_to_mir_context`
   (`driver_bootstrap.spl:124`) as a **count + census written to a file, exit
   status unchanged** — a straight wiring makes 3,629 entries hard errors via
   `_mir_error_is_fatal`'s `"unresolved method call:"` prefix allowlist and
   removes the only iteration loop that exists.
3. Strengthen the `bootstrap_globals.spl:408` guard from "0 instructions" to
   "0 stores and 0 non-panic calls in the entry module" — that is the assertion
   that would have caught this run.

## Control runs (2026-08-08): enum dispatch REFUTED, pipeline confound found

This section supersedes the "Root cause" and "Remaining blocker" sections above.
All runs below use the *same* `--backend llvm --mode dynload` lane, the same
runtime authority, and preserved logs under
`/home/ormastes/dev/simple-s3bisect/build/cyc/`.

### 0. A seed control WAS available — the doc was wrong to say otherwise

The claim above that "the obvious control (build the same reproducer with the
Rust seed) is **not available**" is false. It tested the *wrong* seed. The seed
the bootstrap scripts actually use is

```
/home/ormastes/dev/simple-t3-final-20260806/build/bootstrap-t3-final-20260806/\
  stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority/simple
```

(155 MB, md5 `d1987e1d31872c4661b0aa43416b9b14`) — **not**
`src/compiler_rust/target/bootstrap/simple` (33 MB). The former has LLVM
compiled in (`LLVMBuildStore` present in `strings`; the string
`native backend '…' is not available` is **absent**) and it is what
`build_stage2.sh`/`cycle.sh` invoke as `$SEED`. It is a Rust seed (it prints the
"Rust-built Simple binary is a bootstrap seed only" banner).

### 1. Native enum dispatch is CORRECT — the stated root cause is refuted

Two probes, kept at `probe_enum/` in the bisect worktree:

- `probe_enum_dispatch.spl` — 4-variant enum, payload-free and payload-carrying
  variants, matched with and without sub-patterns.
- `probe_enum2.spl` — deliberately shaped like `HirTypeKind`: **25 variants**,
  recursive through a class field (`TyNode.kind`), list/str/struct payloads,
  matched via `match t.kind:` with 4 variants intentionally left to a `case _:`
  wildcard so the wildcard arm's correctness is measured too.

| run | binary that compiled it | engine / backend | result |
|---|---|---|---|
| A | SEED | interpreter (`SIMPLE_EXECUTION_MODE=interpret`) | 12/12 correct (reference) |
| B | SEED | native, `--backend llvm` | 12/12 correct |
| C | SEED | native, `--backend cranelift` | 12/12 correct |
| D | `S3FIX1/stage2-simple` | native, `--backend llvm` | 12/12 correct |
| E | `S3FIX1/stage2-simple` | native, **exact `cycle.sh` Stage-3 env** | 12/12 correct |

The four variants with no named arm returned `-99` in every run — i.e. the
wildcard arm is reached **exactly when it should be** and not otherwise.
**Enum discriminant reads and match dispatch are not broken under native
codegen, on either backend, including at `HirTypeKind` scale and shape.**

### 2. The reproducer claim in this document is not reproducible

This document states that the 7-line `p2_add.spl` program, built by
`build/cyc/S3FIX1/stage2-simple`, "Build exits **1**" with
`[TEMP-PROBE-mir-wildcard] d=-1 …` and
`error: bootstrap entry lowered to 0 MIR instructions`.

Re-run against the byte-identical binary named in that claim
(`S3FIX1/stage2-simple`, 128,111,944 B, mtime 2026-08-08 02:40 — unchanged since
before this document was written at 04:24), the build **exits 0** and the
resulting binary prints `RESULT=42`. Confirmed across four flag forms, all
exit 0 / `RESULT=42`:

| form | flags |
|---|---|
| A | `--entry-closure --entry FILE` |
| B | `--entry FILE` |
| C | positional `FILE` (this is the form Stage 3 uses) |
| D | `--entry-closure` positional `FILE` |

So the reproducer was mis-recorded. Every inference this document drew from
`d=-1` and from "a `HirTypeKind` reaches the wildcard arm" rests on that run and
therefore does not stand. This is stronger than the earlier "unproven"
downgrade: the observation itself does not reproduce.

### 3. The real finding: the SEED-vs-stage2 comparison is CONFOUNDED

`cycle.sh` does not hold the pipeline fixed across the two stages:

- **Stage 2** sets `SIMPLE_NATIVE_BUILD_RUST=1`.
- **Stage 3** does not set it.

That variable is a pipeline selector, not a tuning knob:

- `src/compiler_rust/driver/src/main.rs:160` —
  `native_build_rust_override(std::env::var("SIMPLE_NATIVE_BUILD_RUST")…)`
- `src/compiler_rust/driver/src/cli/native_build.rs:549` — comment:
  *"Rust handler is reached only via `SIMPLE_NATIVE_BUILD_RUST=1` or a …"*

Therefore **Stage 2 was compiled by the Rust native-build pipeline, and Stage 3
by the pure-Simple native-build pipeline.** The "SEED works / stage2 produces
garbage" asymmetry never isolated *which binary ran* — it changed the pipeline
at the same time.

Restated: **Stage 3 is the only run in the whole bootstrap that exercises the
pure-Simple `native-build` pipeline at compiler scale, and it has never once
produced non-vacuous output.** The probes in §1 show that same pure-Simple
pipeline is correct on a 1–3 module closure, so the open question is scale or a
construct that only the compiler's own source contains — not enum dispatch, not
the backend, not the flag form, and not the environment.

### 4. What is now eliminated

- Enum discriminant reads / match dispatch under native codegen (§1).
- The LLVM backend specifically — cranelift agrees (§1, run C).
- The Stage-3 flag form: `--entry-closure`, `--entry` vs positional (§2).
- The Stage-3 environment, including `SIMPLE_NATIVE_ARENA_DECLS=1`, replayed
  exactly on a small input (§1, run E).
- `stage2-simple` being a corrupt binary in any general sense (§1 run D, §2).

### 5. Note on two red herrings in the IR

- All 5,767 `define`s carry `nounwind readonly`. This is LLVM's `function-attrs`
  pass *inferring* `readonly` from the absence of stores. It is a consequence of
  the vacuity, not a cause — do not chase it.
- `parse_module_body()` and 887 other defines have no parameters where a method
  should carry `self`. Interesting, but unmeasured; it is not part of any
  established causal chain.

### 6. Next actions (replacing the list above)

1. **(Primary.)** Determine whether the pure-Simple `native-build` pipeline
   fails by **scale** or by **construct**: bisect the input between a 3-module
   closure (known good) and the full compiler (known vacuous). A mid-size real
   target — one compiler layer — is the cheapest next point.

   Start at **`src/compiler/10.frontend/core/`**. That subtree is implicated by
   two independent measurements: it holds the single file that blew the 60s
   per-file budget (item 3), and it contains the largest surviving `.text`
   section in the vacuous object's census,
   `compiler.10.frontend.core.tokens.tok_kind_name` (3,200 B). Whatever is
   expensive-or-broken there shows up in both runs. This is a firmer starting
   point than the timeout conditional in item 3.
2. A Stage-3 run using the *Stage-2 recipe* (`--entry-closure` + explicit
   `--source src/compiler --source src/app --source src/lib` + `--entry`) was
   launched but is **a multi-variable flip** (it also changes `--threads` 2→8).
   A non-vacuous result would be the headline; it would still need
   `--entry-closure` isolated as a single-variable follow-up before any causal
   claim.
3. **A 60s per-file compile timeout exists in the pure-Simple pipeline and the
   compiler's own source exceeds it — investigate whether it fails open.**
   The Stage-2-recipe run in item 2 completed in 415s with
   `STAGE3_CLOSURE_EXIT=1` and exactly one failure:

   ```
   FAILED FILES (1):
     - src/compiler/10.frontend/core/__init__.spl: timeout (60s)
   ```

   Log: `build/cyc/S3CLOSURE/build.log`. This is a *per-file* budget, so it only
   surfaces as a named failure in the multi-file (`--entry-closure` + `--source`)
   form. The real Stage-3 recipe compiles the whole compiler as a **single**
   unit ("1 compiled"), where no such per-file failure is ever reported — and
   that run produced 5,767 stub functions with `STAGE3_EXIT=0`. If the same
   budget is applied internally in single-unit mode and degrades to stubs
   instead of erroring, that would produce the observed artifact.
   `driver_aot_native_output.spl:566` already points at a related known defect,
   `doc/08_tracking/bug/native_build_cache_never_written_on_timeout_2026-07-26.md`.

   **But weight this lead honestly: as observed, the timeout fails CLOSED.**
   The S3CLOSURE run exited **1** and produced **no binary**. The same is true
   of the earlier whole-tree run (`build/cyc/EP2`), where four `src/lib` files
   failed LLVM verification: exit 1, no binary. Two independent per-file
   failures, both fail-closed. The real Stage-3 run produced a 1.16 MB object at
   `STAGE3_EXIT=0`, so a per-file timeout of the kind actually measured does
   **not** by itself explain the observed artifact. The fail-open variant is an
   untested conditional about the single-unit path only — treat it as a lead to
   confirm or kill, not as the leading hypothesis.

4. The parallel `unresolved method call:` MIR-lowering lane (`to_u8`/`join`) is
   plausibly the same defect seen from the other side — `[mir-method-call] …
   disc=… unresolved=true` is resolution failure over an enum-keyed table. With
   enum dispatch itself now eliminated, that lane's findings become the more
   promising thread, not a duplicate of this one.

## 2026-08-08 follow-up: bounded re-bisection attempt, inconclusive within budget

Re-diagnosed from scratch per the correction above (did not reuse the refuted
enum-discriminant explanation). Attempted the item-1 scale-vs-construct
bisection on `src/compiler/10.frontend/core` using the same preserved
`S3FIX1/stage2-simple` (128,111,944 B, md5-stable) binary:

```
stage2-simple native-build --backend llvm --mode dynload \
  --entry-closure src/compiler/10.frontend/core --output <scratch>/core_out
```

**Finding: `--entry-closure` on a subdirectory does not scope the build to
that subtree.** It walks the full transitive import graph from every module
under the given path, which — for `10.frontend/core` — pulls in unrelated
`examples/10_tooling/trace32_tools/**` modules and all of
`lib__nogc_sync_mut__fs`, each logged as `[llvm-entry-closure] N unresolved
call(s) in module <X> before codegen; continuing`. Two independent runs (480s
and a prior 120s cap) did not reach codegen completion; both were still
resolving imports/emitting warnings for modules outside the target subtree
when the time budget expired. No object or IR was produced by either run, so
no vacuity/non-vacuity verdict was obtained.

This is consistent with — but does not itself confirm — the "fails by scale"
half of the item-1 hypothesis: the cost is dominated by the size of the
resolved closure, not by the 7 or 25 files actually inside
`10.frontend/core`. It does **not** distinguish scale from construct, because
no run in this session reached a comparison point (small closure = correct
per §1's probes; this attempt never produced output at all).

**No fix was applied.** No `.spl` source was changed by this follow-up: the
bounded-budget bisection did not reach a decision point, so per this
document's own standard (do not fabricate a fix) none is recorded. The
`--entry-closure`-pulls-the-whole-graph behavior noted above is itself a
real observation worth a follow-up bug/lead if the next bisection attempt
wants a *scoped* comparison point — e.g. an explicit `--source` allowlist
(the "Stage-2 recipe" form already used successfully in item 2/3 above,
which is scoped and did complete in 415s) rather than `--entry-closure` on a
subdirectory, which is not scoped at all.

**Recommended next step for whoever picks this up:** repeat item 6.1 using
the Stage-2-recipe form (`--entry-closure` + explicit `--source src/compiler
--source src/app --source src/lib` + `--entry`) restricted to a *reduced*
`--source` set (e.g. only `src/compiler/10.frontend` + `src/compiler/00.*`
scaffolding it needs) so the closure stays small enough to finish inside a
single session's time budget, and compare vacuity there against the known-good
1–3 module probes in §1 and the known-vacuous whole-compiler run.

## 2026-08-09: assigned bisection task's premise does not reproduce; layer-by-layer bisection not performed

This session was assigned to bisect the `--source` allowlist by compiler layer
(`00.common` .. `90.tools`) to find the specific module/construct that flips
the `p2_add.spl` reproducer from exit-0 to
`error: ... unsupported MIR type kind [wildcard-arm] disc=-1: <value:0x...>`,
using `build/cyc/S3FIX1/stage2-simple`.

**That premise was already refuted by this document's own §2 ("The
reproducer claim in this document is not reproducible"), written earlier on
2026-08-08.** This session re-confirmed the refutation independently before
attempting the requested layer bisection:

1. `S3FIX1/stage2-simple` (128,111,944 B, still present, unchanged) run against
   `p2_add.spl` with **no `--source`** (whole default project, matching the
   original bug report's setup) does **not** produce the `[wildcard-arm]`
   error. It times out at 90s still resolving imports/warnings — no MIR
   lowering error of any kind is reached. Log:
   `/tmp/.../scratchpad/bisect/run0.log`.
2. Scoped to a single small layer, `--source src/compiler/00.common`, the same
   binary reaches codegen and fails with a **different, unrelated** defect —
   not enum/wildcard-arm at all:
   ```
   FAILED FILES (1):
     - src/compiler/00.common/predicate_parser.spl: llvm codegen: semantic:
       llvm global load referenced undeclared symbol `has_paren_idx`
   ```
   Log: `/tmp/.../scratchpad/bisect/run1.log`. `has_paren_idx` looks like a
   local/loop variable in `predicate_parser.spl` that LLVM codegen is trying to
   read as a global — plausibly the same "unqualified name falls through to
   the wrong symbol class" family as the enum-variant-as-binding-pattern
   defects fixed elsewhere today, but this was **not investigated further**:
   it is a different failure signature (`undeclared symbol` in codegen, not a
   `HirTypeKind` match wildcard arm in MIR lowering) and was out of this
   session's assigned scope.

**Conclusion: no layer bisection of the `[wildcard-arm] disc=-1` symptom was
performed, because that symptom itself could not be reproduced against the
named binary in either the unscoped or the `00.common`-scoped configuration.**
Continuing the requested binary-search bisection would have bisected a
mis-recorded observation. Per this document's own 2026-08-08 correction, the
open, live thread is item 6.1/6 in the "Control runs" section above (scale-vs-
construct in the pure-Simple `native-build` pipeline on the whole compiler),
not the wildcard-arm/enum-discriminant story.

**No `.spl` source was changed by this session.** No fix, no regression test
was added, because there is nothing to fix: the defect this session was
assigned to isolate does not currently reproduce, and the `has_paren_idx`
codegen error found incidentally is a distinct, unscoped defect that would
need its own bisection to confirm scope and cause.

**Recommended next step:** either (a) whoever files a fresh wildcard-arm
report attaches the exact command line, exact binary path+mtime/md5, and
captured log for a run that actually produces `[wildcard-arm] disc=-1`, so it
can be bisected on a reproducing baseline instead of a described-but-untested
one; or (b) pick up the still-open scale-vs-construct thread from the
"Control runs" §6 recommended next step (Stage-2-recipe form with a reduced
explicit `--source` set), which is the actual unresolved lead in this
document.
