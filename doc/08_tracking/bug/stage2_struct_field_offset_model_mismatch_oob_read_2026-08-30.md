# Stage-2 codegen uses inconsistent struct field offsets across module boundaries (out-of-bounds reads)

Status: OPEN — blocker, NOT worked around
Area: compiler / codegen / bootstrap
Severity: critical — the self-hosted compiler reads struct fields past the end of the allocation

## Symptom

The Simple-compiled Stage-2 compiler fails on a **three-line hello world**:

```
$ ./stage2 compile hello.spl --format=smf -o h.smf
error: in-process SMF compile: MC/DC global byte budget must be at least the owner byte budget
```

The freshly built Rust seed compiles the identical file successfully, so this is
a defect in the compiler Stage 2 produced, not in the input or the environment.

Stage 2 itself builds cleanly beforehand: `821 compiled, 0 cached, 0 failed`,
136 MB linked. The binary is well-formed; it is *wrong*.

## This is NOT an MC/DC configuration problem

The error text is a red herring. The MC/DC defaults are self-consistent
(`config.spl:89-105`: `mcdc_owner_bytes: 1048576`, `mcdc_global_bytes: 67108864`),
no `SIMPLE_MCDC_*` variables are set, and **setting the env override does not
help** — because `config.spl:149` gates the override on a comparison between two
values that are themselves read from the wrong offsets.

## Root cause: two different field-offset models for the same struct

Measured by disassembling the Stage-2 binary (symbols intact) and confirmed by
patching and re-running it.

| site | observation |
|---|---|
| `CompilerConfig.default` @ `0x100028288` | `mov w0, #0x70; bl _rt_alloc` — allocates **112 bytes**; writes owner/global as one `stp` pair at **[0x50]/[0x58]** |
| `CompileContext.create` @ `0x1006a0d20` | `ldp x9, x8, [x20, #0xd0]` — reads owner/global at **offset 208**, i.e. **96 bytes past the end** of that 112-byte object |
| `compileoptions_normalize_mir_optimization` @ `0x100029380` | `CompileOptions`: `mcdc_mode_text@0xa8`, `owner@0xb0`, `global@0xb8` |
| `CompileContext.create` | same `CompileOptions`: `mode_text@0xa8` (agrees) but `owner@0xd0`, `global@0xd8` — a **+0x20 disagreement** on the very next fields |

Both offsets were re-verified independently from `otool -tv` output.

## Runtime confirmation (patched binaries)

1. The diagnostic string exists twice in the binary. Tagging the two copies
   distinctly shows the stock binary fires `driver_types.spl:568` — the
   `options.mcdc_global_bytes > 0` branch.
2. Forcing that branch's `b.lt` open makes `:570` fire instead, proving
   `compiler_config` is *also* read wrongly, not just `options`.
3. Forcing **both** gates open reaches MIR and dies with
   `MCDC-E-BUFFER-CAP: mcdc_global_bytes must be a positive integer, got '0'`.
   So `compiler_config.mcdc_global_bytes` genuinely reads **0**, not 67108864.
4. Immediate-comparison probes (1, 2, 5, 4095, 65536, 1048576) all still fail,
   bounding the corrupt `options.mcdc_global_bytes` at **>= 2^20**.

## Why this matters far beyond MC/DC

The MC/DC check is merely the first place the mismatch happens to be *observable*
— it is a comparison whose result changes behaviour. The defect itself is
generic: **the same struct type has different field offsets in different
functions**, and one of the models reads outside the allocation. Any cross-module
struct field access compiled by this Stage 2 may silently read adjacent heap
memory. That is a memory-safety-class defect, and any Stage-3 artifact this
compiler produces is untrustworthy regardless of whether it links.

This is also exactly the shape of failure that "verify by symbol count/banner,
never exit code" warnings in `.claude/rules/bootstrap.md` exist for: a binary can
be produced, be correctly sized, link cleanly, and still be wrong.

## Deliberately NOT worked around

A defensive clamp in `driver_types.spl` / `config.spl` would make the lane
proceed. It was drafted and rejected: it masks an out-of-bounds read rather than
fixing it, and would hand Stage 3 a compiler with the same latent defect while
making the lane look green. Per the repo's own standard — a gate that reports
success it did not verify is worse than no gate — the lane stays red until the
offset model is fixed.

## Platform scope

**Unmeasured on Linux; do not assume this is macOS-specific.** The eight defects
found alongside it in this lane were all macOS-only, but this one is different in
kind: an offset-model disagreement in Stage-1's codegen is target-independent by
nature, so Linux Stage 2 is expected to be equally affected. Confirming that on a
Linux host is the single highest-value next measurement.

## Next steps

1. Measure on Linux. If it reproduces, this is not a platform issue at all and
   the priority changes.
2. Find why `CompileContext.create` resolves a different layout for
   `CompilerConfig` and `CompileOptions` than their own constructors do. The
   `mcdc_mode_text@0xa8` field *agrees* while the next two disagree by 0x20,
   which suggests a divergence introduced partway through the field list rather
   than a wholesale different type.
3. Nearest existing record by shape:
   `bootstrap_stage2_hir_field_type_inference_regression_2026-08-13.md`
   (imported-type provenance loss in HIR).

## Reproduction

```
# 2 seconds, no bootstrap run required
cp build/bootstrap/stage2-rejected/<triple>/simple /tmp/stage2 && chmod u+x /tmp/stage2
printf 'fn main():\n    print("hi")\n' > /tmp/hello.spl
/tmp/stage2 compile /tmp/hello.spl --format=smf -o /tmp/h.smf
```

Control (succeeds): the Rust seed under `build/phase_snapshots/phase1_*/simple`.

## Update 2026-08-30 (evening): root cause found and largely fixed

The receiver-blind "most fields wins" search was the mechanism, but not the
cause. The cause was that types imported via `export use` were never registered,
so `resolve_type` degraded them to `TypeId::ANY` and the heuristic ran at all.

Fixed in sequence, each verified before the next:

1. `module_pass.rs` — Pass 0.5a/0.5b walked only `Node::UseStmt`, never
   `Node::ExportUseStmt`. `driver_types.spl:7` is `export use ...*`, its ONLY
   route to `CompileOptions`. Result: `options` now reads `CompileOptions`
   field 22 (0xb0) instead of `MirLowering` field 26 (0xd0).
2. `imports.rs` — the whole-program return-type map walked only `Node::Function`,
   so no `impl`-block method had a declared return type; `CompilerConfig.from_env`
   had no row.
3. `stmt_lowering.rs` / `context.rs` / `access.rs` — hint a local's struct type
   from its static-call initializer's DECLARED RETURN TYPE (not the callee name,
   which would mis-hint `Foo.parse() -> text`).
4. `imports.rs` again — fix (2) landed inside the FIRST of two `for item in
   &ast.items` matches, shadowing the pre-existing `Node::Impl` arm at :622 that
   was the sole producer of `raw_to_mangled` entries. That produced ~778
   unqualified `Type.method` link errors. Un-shadowed; link now green.

Result: Stage 2 links (821 compiled, 0 failed, 136 MB) and the binary runs,
reporting `simple-bootstrap 1.0.0-rc.1`. This is the furthest the macOS lane has
reached.

### Still open

Stage 2 is REJECTED at sanity: the binary HANGS on a three-line hello world.
It compiles cleanly (`[bootstrap-error-count]` 0 at entry, post-lowering,
post-diagnostics, post-store) and then spins. macOS `sample`, 2161 samples, all
on one call site:

    compiler__mir_opt__mir_opt__storage_projection_lowering__
      lower_mir_storage_project_fields_v1 (+288)
        2001  rt_range (+80)
          61  rt_array_push_grow (+8)

The loops in that file are bounded by `binding.fields.len()`
(storage_projection_lowering.spl:86,94). A garbage field read there yields a
huge bound and an effectively infinite loop — the same defect class as above.

**Note the heuristic is still live.** The fail-closed guards were reverted
because they broke 47 files (erasure to ANY is pervasive), so "most fields wins"
still resolves every other ANY receiver. The MIR structs this pass reads may
still be misresolved. Whether this hang is that, or a pre-existing pathology in
a pass no macOS build had ever reached, is UNDETERMINED at time of writing.

Discriminator note: comparing against an earlier seed does NOT settle it — the
seed is the Rust compiler and never executes this pass, which is Simple code
compiled into Stage 2. No working macOS Stage 2 existed before today.

## Update 2026-09-06 (Linux aarch64): reproduced WITHOUT a bootstrap, and largely fixed

Next-step #1 above ("measure on Linux") is done, and the answer is that this is
**not a macOS issue and not a Stage-2 issue**. The defect is in the Rust seed's
own HIR lowerer and reproduces on the seed's Cranelift JIT in two seconds, with
no bootstrap, no Stage-2 artifact, and no disassembly.

### Reproduction (aarch64 Linux, seed at src/compiler_rust/target/release/simple)

`/tmp/zz2.spl`:

```
struct ZzSmall:
    zzq: i64

struct ZzBig:
    p0: i64
    p1: i64
    p2: i64
    p3: i64
    zzq: i64

fn read_zzq(o: any) -> i64:
    return o.zzq

fn main():
    var s = ZzSmall(zzq: 42)
    print(read_zzq(s))
```

```
$ SIMPLE_TRACE_FIELD_GET=1 bin/simple run /tmp/zz2.spl
[FIELD-TRACE] ANY/zzq -> LOCAL-BEST idx=4 count=5 in zz2.spl
[TRACE FieldGet] dest=VReg(2) object=VReg(0) byte_offset=32 field_type=TypeId(5) func=read_zzq
3257846563034067813
```

Expected `42` at `byte_offset=0`. Observed `byte_offset=32` — 32 bytes past the
end of `ZzSmall`'s single 8-byte payload slot — and the value read,
`3257846563034067813` = `0x2d363230325f7365`, is the little-endian ASCII
`"es_2026-"`: a fragment of an adjacent heap string constant. That is the
out-of-bounds read, observed as a wrong value, not inferred from a suspicious
offset.

Deleting `ZzBig` (leaving one candidate) restores `byte_offset=0` and `42`, so
the offset is a function of what other structs are in scope, not of the
receiver.

**Interpreter caveat that will make this look fixed when it is not:** the
tree-walking interpreter resolves fields by name and always answers `42`. The
test runner exports `SIMPLE_EXECUTION_MODE=interpret` /
`SIMPLE_RUNTIME_MODE=interpreter`, and a child `bin/simple run` inherits them —
a spec that shells out without `env -u`-ing both passes vacuously on a broken
binary. Measured directly while writing the regression spec below.

### The two offset models, quoted

* **Model A — declaration-driven (correct).** `get_field_info`'s
  `HirType::Struct` arm, `src/compiler_rust/compiler/src/hir/lower/type_resolver.rs:781-806` (line numbers in this section are as of the fix commit):
  the field's index **in its own declared struct**. This is what the
  constructor and every typed receiver use (macOS: owner/global at `0x50/0x58`).
* **Model B — receiver-blind "most fields wins" (the defect).** The `TypeId::ANY`
  and `HirType::Any` arms of the same function (the `is_none_or` tie-breaks now
  at `type_resolver.rs:685` and `:750`): scan every struct in `module.types` for
  the field NAME and keep the candidate with the largest `fields.len()`, i.e.
  deliberately the LARGEST index. The identical rule ran at five more sites —
  `type_resolver.rs:104` (`resolve_global_field_info`, the cross-module set),
  `:862`, `:962`, `:977`, and `hir/lower/expr/access.rs:433`.

Field slots are a uniform 8 bytes — `byte_offset = (field_index as u32) * 8` at
`mir/lower/lowering_expr_struct.rs:328`, `mir/lower/lowering_stmt.rs:539`,
`mir/lower/lowering_expr_method.rs:1421` — so Model B's largest index is out of
bounds for **every** candidate smaller than the winner, while Model A's is by
construction in bounds. That is the whole divergence: 22 (`CompileOptions`) vs
26 (`MirLowering`) is exactly the `0xb0`/`0xd0` pair recorded above.

The correct rule was already written down, and applied to only one of the two
paths: `pipeline/native_project/compiler.rs:694-707` computes
`ambiguous_field_names` as "a field name is ambiguous *only* when two structs
disagree on its index within the struct" — but it feeds only the GLOBAL lookup,
is gated on `populate_global_struct_defs` (`--entry-closure` builds only), and
the local `module.types` scan has no ambiguity check at all. Cross-module types
are registered into `module.types`, so they funnel into the unchecked path.

### Fix applied

Tie-break changed from "most fields" to **smallest index** at all six sites
(count retained only to break ties between candidates that agree on the index,
which produce an identical byte offset either way).

The property this buys is provable, and is stated as what it is — a
memory-safety guarantee, not a correctness one. For any candidate `C` that
declares the field at index `i_C`, the chosen `i = min i_C` satisfies
`i <= i_C < len(C)`, so with uniform 8-byte slots the load at `8*i` is inside
`C`'s allocation for every candidate. Most-fields-wins had exactly the opposite
property. When the actual receiver is the *larger* struct the read is still the
wrong field — but in bounds, and no longer a memory-safety defect.

**Not claimed:** that this fixes the Stage-2 hang in
`lower_mir_storage_project_fields_v1`. That needs a bootstrap, which was not run.
`SIMPLE_SEED_FIELD_GUARD` (the `rt_struct_receiver_valid` bounds guard at
`codegen/instr/fields.rs:30-53`) is not usable as evidence here: it false-positives
on a correct offset-0 read in the seed JIT.

The stricter alternative — fail closed on index disagreement, mirroring
`compiler.rs:694-707` — was NOT taken: the ANY branch's error path degrades to a
dynamic `MethodCall` that links to nothing, which is the "broke 47 files"
outcome recorded in the 2026-08-30 evening update.

### Regression specs

`test/03_system/compiler/native_struct_field_access_regression_spec.spl` gains
two scenarios (repro + a declaration-order generalization with three candidates
at indices 0/2/5, so a green verdict cannot be registry-iteration luck).

* before: `Results: 3 total, 0 passed, 3 failed`
* after:  `Results: 3 total, 2 passed, 1 failed`

The remaining failure is that file's pre-existing scenario 1, which fails
identically on both binaries: `bin/simple native-build --entry` over the
compiler source closure dies with `MIR lowering error: unsupported MIR type kind
[infer-arm]` / `export use` resolution errors in
`src/compiler/70.backend/backend/mir_to_llvm.spl`. Unrelated to this change and
untouched by it.

### Blast radius, measured (not asserted)

The tie-break change is memory-safe by construction but is NOT correctness-
preserving: a pick whose actual receiver was the largest candidate was right
under most-fields-wins and is now a different (still in-bounds) field. That
population was counted rather than guessed, by diffing the `[FIELD-TRACE]`
resolution lines of the same program under both binaries in the same tree:

| corpus (`bin/simple run`, `SIMPLE_TRACE_FIELD_GET=1`) | ANY picks | picks whose index changed |
|---|---|---|
| `src/app/sspec_maintain/main.spl scan test/01_unit/compiler/backend` | 7 | **4** (`coverage` 5->4, `doc_lines` 5->2, `status` 3->0, `title` 5->0) |
| `src/app/spipe_docgen/main.spl --help` | 7 | **2** (`doc_lines` 5->2, `status` 3->0) |

So the change is live on real code, not just the fixture. Neither corpus runs to
completion on either binary (both die in a pre-existing `stack overflow:
recursion depth 1000 exceeded ... in function 'at_end'`), so end-to-end output
could not be compared; the specs that do run were identical on both binaries
(`global_c_repr_struct_field_read_spec` 5/5 both, `struct_init_field_order_fill_spec`
6/8 both, `native_cross_module_class_field_layout_regression_spec` 1/3 both,
`cargo test -p simple-compiler --lib hir::lower` 288/288 both).

The right end state is still to stop erasing these receivers to ANY, so the
fallback never runs — this change only makes the fallback stop reading outside
the object while that work is outstanding.
