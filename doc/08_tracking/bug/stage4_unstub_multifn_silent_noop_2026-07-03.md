# stage4 unstub path: multi-function run files silently no-op (deploy rolled back)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


---

## Verification 2026-11-25 (P2 sweep lane) — STALE / RESOLVED

The "OPEN — blocks re-deploy" status header is stale. This exact defect was
root-caused and fixed as **iteration 19 (#85)** of
`stage4_codegen_compact_form_hazards_2026-07-02.md` (2026-07-03, same day):
`HirModule.functions` dict keys collapsed because `SymbolTable.lookup()`
returned a shared/corrupt `SymbolId` struct handle on stage4; the second
function overwrote `main`, so the module silently no-opped. Fixed by keying
`functions` with a distinct synthetic `SymbolId(id: lower_idx)`
(commits 95f504162fc / 370e379b6a0) plus a by-name user-fn call fast-path in
the interpreter `Call` arm; verified on a fresh probe-free build with the
exact repro shape from this doc (`fn helper()` + `fn main()` → `m1` /
`plain-helper`, rc=0) and a 3-function file.

Code-inspection check at release/1.0.0 HEAD (`64dfa6d980f`): the synthetic-key
lowering is present in its evolved form in
`src/compiler/20.hir/hir_lowering/_Items/module_build.spl:616-740`
(`lower_idx` loop; the comment at :730 still cites the stage4 seed
struct-value collision rationale).

Behavioral re-verification is environment-blocked here: the original smoke
required a self-hosted Linux stage4 binary (full bootstrap), and the pinned
`bin/simple.exe` cannot run `test` at this HEAD
(`@representation_boundary` seed/binary inconsistency). Status: **RESOLVED**.
