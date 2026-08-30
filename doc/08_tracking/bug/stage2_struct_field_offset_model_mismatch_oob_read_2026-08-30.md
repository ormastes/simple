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
