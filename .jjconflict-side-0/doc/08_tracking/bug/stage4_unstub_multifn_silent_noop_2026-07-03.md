# stage4 unstub path: multi-function run files silently no-op (deploy rolled back)

**Date:** 2026-07-03 · **Status:** OPEN — blocks re-deploy of the unstubbed stage4

## Milestone context
The #59 chain reached its goal: stage4 executes `-c "print(1+1)"` → `2` with real
HIR lowering (18 iterations, ~21 root causes; see
`stage4_codegen_compact_form_hazards_2026-07-02.md`). Flip commit `3db42a3a05a6`
made real lowering the default (`SIMPLE_STUB_HIR=1` escape hatch) and the binary
was deployed. Initial 5-point smoke passed (-c, single-fn run, --version,
lint rc=0, target_presets spec).

## Regression found in extended smoke
Any run file with **more than one function** silently no-ops on the unstub path:

```
fn helper() -> text:
    "plain-helper"

fn main():
    print("m1")
    print(helper())
```
- old binary (simple.bak-20260702): prints `m1` / `plain-helper`
- unstubbed stage4_deploy2: prints NOTHING, rc=0 (main never executes or whole
  module lowers empty)

The entire iteration chain only ever smoked single-function files (`-c`
synthesizes one main; hello_it15.spl is one fn). Not @cfg-related (plain file
reproduces; forcing SIMPLE_TARGET_ARCH changes nothing).

## Also fixed en route (committed, real)
- `cfg_detect_arch` called extern `rt_get_host_target_code` which was **never
  implemented** in the runtime → null indirect call crashed every @cfg-bearing
  file on any stage4 binary containing cb8d9df7035. Fixed: `69fc23136c82`
  (/proc/sys/kernel/arch via rt_file_read_text) + runtime impl committed for
  the next seed redeploy (#79). Other callers (backend_selector.spl:203,
  sffi/ffi system.spl) remain latent null-calls until #79 exports the symbol.

## Action taken
Deploy protocol restore executed: `bin/release/x86_64-unknown-linux-gnu/simple`
← `simple.bak-20260702`; verified multi-fn run, --version, target_presets PASS.
Milestone binaries preserved in session scratchpad (`stage4_deploy2`,
`stage4_it18z2/z3`). All fixes are on `main`.

## Next (iteration 19)
Make multi-function modules execute on the unstub path: suspect the
functions-dict iteration / synthetic-main selection in
`interpreter.spl::process_module` (`values()` + `f.name == "main"`), or
lower_parser_module_unstub dropping non-main functions. Then extend the smoke
matrix (multi-fn, @cfg, struct/class, imports) BEFORE any re-deploy, and flip
the default again only after the matrix passes.
