# Stage 3 "vacuous binary" is enum-discriminant garbage in stage2, NOT a link failure

Date: 2026-08-08
Status: OPEN — Stage 3 cannot produce a genuine self-hosted binary
Severity: BLOCKER (critical path to self-host)

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

## Root cause: garbage enum discriminants in the natively-built stage2

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

## Remaining blocker (stated plainly)

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
