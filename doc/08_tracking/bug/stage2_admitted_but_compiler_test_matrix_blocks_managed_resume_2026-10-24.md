# Stage 2 is ADMITTED on release/1.0.0; the mandatory compiler-test matrix blocks Stage 3/4

- **Date:** 2026-10-24
- **Status:** OPEN — blocker is a single module, named below
- **Lane:** `release/1.0.0`, Linux x86_64, `--backend=cranelift`, strategy `adhoc`
- **Good news first:** Stage 2 admission now SUCCEEDS on this branch. That had
  been blocked all session.

## What now works

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --strategy=adhoc --backend=cranelift \
  --full-bootstrap --stop-after-stage2 --invalidate-cache=stage2 \
  --produce-stage3-receipt=verify-landed-compiler-fix \
  --produce-managed-receipt=self-host-convergence-check
```

reaches, in order: `Cache: reused 0 modules; rebuilt 1487` ->
`PASS — 1 binary(ies) checked, 0 tombstone reference(s)` -> bootstrap compiler
sanity -> struct receiver/runtime capability -> **both admission receipts
published**:

| receipt | bytes |
|---|---|
| `stage3-planner-admission.receipt` | 2849 |
| `managed-stage4-planner-admission-v2.env` | 2850 |

Admitted candidate sha256 `206bfd58409c78ca3015d45276c7333ee0909a47452995cbc653126deb9da3af`,
`compiler_hash_status=PASS` (expected == actual).

Two landed fixes are what made this possible, neither of them mine:

- `0e2d7ab2997` "fold walkers unwrap optional node payloads (Stage 2 [] SIGSEGV)"
  — cleared the `stage2_module_path_naming` probe.
- PR #4249 "unwrap restored env snapshots explicitly (Stage 2 route gate)" —
  applied locally for this run; it fixes the restore failure that hit the
  **positional** `hello_world_positional` probe, the fifth and last sanity probe.
  **This run is native evidence for that PR**, which was still awaiting it.

Both receipt flags can be passed in one `--full-bootstrap --stop-after-stage2`
invocation and both producers run (`bootstrap-from-scratch.sh:4690`, `:4720`),
so there is no need for a second Stage 2 lane to obtain them.

## What blocks Stage 3/4

The run then aborts:

```
Stage 2: compiler tests (phase verification matrix, strategy=normal, profile=slim,
         timeout=3600s, build-threads=1, test-workers=1)
error: Stage 2 compiler tests failed (status=1)
       The Stage 2 admission receipt, parent receipts and runtime
       capsule were published before these tests ran and remain on
       disk; do NOT resume Stage 3 from this output until the
       failure above is understood.
VERDICT — ABORTED: stage=stage2-compiler-tests exit=1 signal=none reason=stage2-compiler-tests
```

and the managed resume is refused, fail-closed:

```
stage2-tests-resume: retained compiler-test rejection blocks managed resume
managed-resume: mandatory Stage 2 compiler-test matrix not admitted
```

**The matrix is MANDATORY.** Understanding the failure is not sufficient — the
rejection must be cleared. Record this explicitly because the surrounding
evidence invites the opposite conclusion (see "A wrong turn" below).

## The single failing module

From `verification/summary.env`:

| key | value |
|---|---|
| `module_compile_inventory_count` | 14735 |
| `module_compile_selected_count` | 14728 |
| `module_compile_sealed_count` | 7 |
| `module_compile_retained_failed_count` | **1** |
| `failed_tool_module_limit` | 8 |
| `terminal_failures` | 8 |
| `overall` | FAIL |

Eight modules were attempted; exactly one failed:

```
task=module_compile_3|entry=src/app/_cg/f07/main.spl|result=FAIL|status=1
```

`src/app/_cg/f07/main.spl` is 10 lines of ordinary `Result`:

```simple
fn half(n: i64) -> Result<i64, text>:
    if n % 2 == 0: Ok(n / 2)
    else: Err("odd")
fn run(n: i64) -> Result<i64, text>:
    val h = half(n)?
    Ok(h + 1)
fn main() -> void:
    match run(8):
        case Ok(v): print(v.to_text())
        case Err(e): print(e)
```

Its retained compile log gives exactly three errors, matching the three
construction sites:

```
[ERROR] MIR error: MIR lowering error: enum construction 'Result::Ok': missing declared payload metadata
[ERROR] MIR error: MIR lowering error: enum construction 'Result::Ok': missing declared payload metadata
[ERROR] MIR error: MIR lowering error: enum construction 'Result::Err': missing declared payload metadata
[build] phase=mir state=failed ... current=lower_to_mir
```

**The `match` arms and the `?` operator did NOT error.** Only construction did.
Pattern matching resolves the same variants, so a working reference path for
this metadata exists in-tree.

Error site: `src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl:177-189`,
`enum_positional_payload_reason`. `enum_variant_discriminant` resolves (no
"unknown variant"), but `enum_variant_payload_kind` / `enum_variant_payload_types`
have no `Result::Ok` entry. Immediately above, `enum_payload_key_uses_declared_slots`
(`:168-175`) deliberately treats a GENERIC owner as not using declared slots, so
a builtin generic `Result` reaching the metadata-requiring path looks like the
defect — **not established**, under investigation.

## Also in the matrix, and expected

```
task=compiler_bootstrap_tests|result=UNSUPPORTED|status=full-cli-artifact-not-built
task=interpreter_interpreter_tests|result=UNSUPPORTED|status=full-cli-artifact-not-built
task=loader_interpreter_tests|result=UNSUPPORTED|status=full-cli-artifact-not-built
```

Not failures: Stage 2 is the bootstrap CLI, which exposes only `compile` and
`native-build`, so there is no full-CLI artifact to drive.

## A wrong turn, recorded so it is not repeated

The module is outside the compiler's own source closure — `_cg/f07` appears **0**
times in `stage2-native-build.log`, and nothing under `src/compiler` or
`src/app/cli` references `app._cg`. From that I concluded Stage 3 was unaffected
and attempted the managed resume. **The gate refused it, correctly.** Being
outside the Stage 3 closure does not make the matrix optional; the matrix is a
conformance sweep over the whole source tree and its rejection is retained
state. Do not plan around it.

Equally: a chain that fires the managed resume on the strength of the published
receipts is wrong, because the receipts are published BEFORE the matrix runs and
are not retracted by its failure. The script's own warning says so.

## What the campaign does NOT establish

The campaign stopped at the `failed_tool_module_limit=8`, so **14,720 of 14,728
selected modules were never attempted**. There is no basis for claiming the rest
compile. Fixing `_cg/f07` admits the next 8-module window, not the matrix.

## Next step

Fix the generic-enum construction path so `Ok(...)` / `Err(...)` lower, then
re-run the Stage 2 lane. Each verification costs a full Stage 2 rebuild
(~40 min on this host), because the defect is in the pure-Simple self-hosted
compiler (`src/compiler/50.mir/**`) and only takes effect in a rebuilt Stage 2
binary — the Rust seed does not use that code path.
