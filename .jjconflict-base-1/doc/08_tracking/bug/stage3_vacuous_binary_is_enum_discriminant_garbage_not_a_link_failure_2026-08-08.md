# Stage 3 "vacuous binary" is enum-discriminant garbage in stage2, NOT a link failure

Date: 2026-08-08
Status: OPEN — Stage 3 cannot produce a genuine self-hosted binary
Severity: BLOCKER (critical path to self-host)

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

1. Determine whether the pure-Simple `native-build` pipeline fails by **scale**
   or by **construct**: bisect the input between a 3-module closure (known good)
   and the full compiler (known vacuous). A mid-size real target — one compiler
   layer — is the cheapest next point.
2. A Stage-3 run using the *Stage-2 recipe* (`--entry-closure` + explicit
   `--source src/compiler --source src/app --source src/lib` + `--entry`) was
   launched but is **a multi-variable flip** (it also changes `--threads` 2→8).
   A non-vacuous result would be the headline; it would still need
   `--entry-closure` isolated as a single-variable follow-up before any causal
   claim.
3. The parallel `unresolved method call:` MIR-lowering lane (`to_u8`/`join`) is
   plausibly the same defect seen from the other side — `[mir-method-call] …
   disc=… unresolved=true` is resolution failure over an enum-keyed table. With
   enum dispatch itself now eliminated, that lane's findings become the more
   promising thread, not a duplicate of this one.
