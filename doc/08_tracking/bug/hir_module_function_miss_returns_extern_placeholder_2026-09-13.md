# `hir_module_function` returns an `is_extern: true` placeholder on a miss, so a failed lookup is silently a skipped function

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-5, `work/bootstrap-full-3-2026-09-12`
- Severity: fail-open. A lookup failure is reported three phases later as
  `MIR module has no functions`, with nothing naming the module, the symbol, or
  the lookup.
- Not fixed here: `src/compiler/50.mir/_MirLowering/module_lowering.spl` is
  FENCED for this lane (`scratchpad/egl_offlimits_v2.txt`).

## Shape

`MirLowering.hir_module_function(module, symbol)`
(`module_lowering.spl:755`) resolves a `SymbolId` by scanning
`module.functions.values()` for a matching `symbol.id`. On **either** failure
mode — `symbol.id < 0`, or no value matches — it returns a fabricated
`HirFunction` with `name: ""`, an empty body, and **`is_extern: true`**.

The only caller that can miss is the bootstrap-flat function loop
(`module_lowering.spl:1414-1454`), which is the one loop that iterates
`module.functions.keys()` and re-finds each value instead of iterating
`.values()` directly like the ordinary loop at `:1716`. Its very next line is

    if not self.hir_function_is_extern(fn_):

so the placeholder is indistinguishable from a real `extern fn` declaration and
the function is skipped. The module then contributes zero MIR functions and the
AOT backend fails far away with

    AOT compile error in <module>: MIR module has no functions

## Measured

Stage-2 binary `scratchpad/boot5/pin/simple.stage2.rejected`, sha256
`79139f420ee07450...`; scrubbed sanity environment plus
`SIMPLE_COMPILER_PHASE_PROFILE=1 SIMPLE_INTERP_TRACE=1`; building
`scripts/check/cert/redeploy_gate/fixtures/hello_world.spl` (a two-line file
whose only function is `fn main()`), with `SIMPLE_BOOTSTRAP=1`:

    [mir-lower] lower_module:start module=...hello_world.spl functions=1
    [mir-lower] functions:count 1
    [mir-lower] function-index 0
    [mir-lower] function-symbol
    [mir-lower] function-loaded      <- no `function:start`, so is_extern was true
    [mir-lower] lower_module:done

`functions:count 1` proves the key existed; `main` is not `extern`; the loop
still skipped it. The key came from `module.functions.keys()` of the same
`Dict<SymbolId, HirFunction>` that was then scanned — so a key did not find its
own value.

## Two defects, stated separately

1. **The fail-open.** A miss must be an error naming the module and the symbol,
   not a synthetic extern. As written, ANY future miss degrades silently into a
   dropped function.
2. **The miss itself.** A key taken from `keys()` failing to match any value's
   `symbol.id` in the same dict is a real defect on this native binary and has
   not been root-caused here. The ordinary loop at `:1716` never hits it because
   it iterates `.values()` and needs no lookup.

Only the routing that sent a non-bootstrap module into this loop was fixed
(`bootstrap_mode_assumes_bootstrap_cli_probe_chain_2026-09-13.md`, site 3).
Both defects above survive that fix and will fire again for any module the
bootstrap-flat path legitimately lowers.

## Reproduction (about 30 seconds, no bootstrap needed)

    sh scratchpad/boot5/disc5.sh bs1_trace
    grep '\[mir-lower\]' scratchpad/boot5/d_bs1_trace.log
