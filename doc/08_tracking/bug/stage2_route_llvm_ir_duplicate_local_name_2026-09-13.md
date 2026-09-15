# Site 11: the Stage-2 route now REACHES llc and emits invalid IR (duplicate local name)

- **Status:** FIXED (2026-09-13) — the three `Ret`-arm reads now use
  `?? ssa_unreachable_operand_fallback()`, landed on `main` via PR #794
  (`ccd13727443`); this record's measurement below is the BOOT-10 evidence.
  Verified by a full
  canonical `--stop-after-stage2` bootstrap, see "Closed by measurement" below.
- **Lane:** BOOT-9, found on `build/bootstrap-boot9b` (09:43:56 -> 09:52:48,
  head `c541c610d86`, `--full-bootstrap --backend=llvm --mode=dynload --jobs=10
  --stop-after-stage2`)
- **Severity:** the current `--stop-after-stage2` admission blocker, successor to
  sites 9 (`stage2_stage3_route_native_compile_timeout_2026-09-13.md`) and 10
  (`stage2_unwrap_on_array_pop_yields_nil_2026-09-13.md`), both fixed.
- **Candidate:** `build/bootstrap-boot9b/stage2/aarch64-unknown-linux-gnu/simple`,
  sha256 `99ba0cf430d255a4141edfc7...`, 152198144 B (pin
  `scratchpad/boot9/pin/cand.boot9b.stage2`).

## The failure kind CHANGED, which is the progress

Sites 9 and 10 both showed as `status 124` — the route was killed by the gate's
180 s ceiling while allocating without bound. It now fails as `status 1` with a
concrete diagnostic, in seconds:

```
| error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
| /usr/lib/llvm-18/bin/llc: error: .../simple-llvm-aot-*/module.ll:102:3:
  error: multiple definition of local value named 'l13'
error: in-process native-build: build failed: 2 failed, 0 unverified, 0 not run,
  0 ok of 2 unit(s) — ERROR:
  scripts.check.cert.redeploy_gate.fixtures.stage2_module_path_naming,
  compiler.common.module_path_naming
```

Both units fail the same way. Reproduced standalone in seconds with the gate's
own env and fixture (`scratchpad/boot9/route11.log`, `route11b.log`).

## One variable: which compiler emits the IR

| compiler emitting the IR | result |
|---|---|
| the bootstrap's LLVM-capable **Rust seed**, `--backend llvm`, same fixture, same runtime authority, same flags | **PASS** — `1 compiled, 0 failed`, and the produced binary prints exactly the fixture's EXPECT block: `app.cli.bootstrap_main` / `compiler.driver.driver` / `app.cli.main` (`scratchpad/boot9/seed_fixture_build.log`) |
| the **Stage-2 candidate** (pure-Simple emitter) | FAIL — `multiple definition of local value named 'l13'` |

So the defect is in the pure-Simple LLVM text emitter's local-value naming, not
in the fixture, the MIR, the runtime, llc, or LLVM 18. Locals are named `l<N>`
from MIR local ids (`src/compiler/70.backend/backend/_MirToLlvm/`), so a
duplicate `l13` means one MIR local id is DEFINED twice inside one function
body without renaming — LLVM text IR requires each local value name to be
defined exactly once per function.

## MEASURED AND FIXED 2026-09-13 (BOOT-10) — cause, repro, fix

**Cause: the alloca-slot transform refuses every function whose terminator is
`Ret(Some(<local>))`, in the candidate only.**

`ssa_alloca_transform_blocks`'s third admission gate is
`ssa_term_operand_payloads_valid` (`var_reassign_ssa.spl:937-947`), whose `Ret`
arm read the optional operand as `value.unwrap()`. On the staged-native LLVM
lane `.unwrap()` lowers to `rt_enum_payload`, which yields nil/raw 0 — the
defect already filed as
`stage2_unwrap_on_array_pop_yields_nil_2026-09-13.md` (site 10) and documented
in this very file's own `Call` arm (`:1216`, "`??` NOT `.unwrap()`: a bare
`unwrap` published by another module steals every Option.unwrap binding on this
lane and returns raw 0"). So `ssa_operand_local_payload_valid(nil)` -> false ->
`reject("invalid terminator operands")` -> the transform never runs -> every
multi-def local is emitted as a duplicate `%lN`.

`module_logical_name_from_path`'s `var mod_path` is written **10 times** (`%l14`
in the retained IR), which is the reported `l13`/`l14`.

### Retained IR (guide step 1 is now landed)

`llvm_object_stage_fail` (`llvm_backend_tools.spl`) now honours
`SIMPLE_KEEP_LLVM_IR=1` on the FAILURE paths and appends the retained staging
dir to the diagnostic; the default still removes it. For the candidate (which
predates the knob) the IR was captured with an `llc` shim on PATH that copies
every `*.ll` argv before exec'ing the real llc — `find_llc` resolves a bare
`llc` from PATH (`find_llc: env_dirs=0 first=<none> resolved=[llc]`).

### One variable: the terminator's operand

Measured with the pinned candidate (`sha256 99ba0cf430d255a4`, 152198272 B) on
the gate's own env, aarch64, llc 18:

| fixture | function | terminator | allocas | duplicate `%lN` |
|---|---|---|---|---|
| `var s = "a"; s = s + "b"; print(s)` in `main` | `@__simple_main` | `ret i64 0` (Ret(None)) | **1** (`%l5 = alloca ptr` + store/load) | **0** |
| same reassignment inside a `while` in `main` | `@__simple_main` | `ret i64 0` | **1** | **0** |
| 5-line fn, ONE reassignment in ONE `if`, returns text | `@shape` | `ret ptr %l1` | **0** | **1** (`%l1` in bb0 and bb2) |
| same, returns `i64` | `@shape` | `ret i64 %lN` | **0** | 1 |
| same, declared `-> ()` (still lowers to an i64 return) | `@shape` | `ret i64 %lN` | **0** | 1 |
| the gate's real fixture | `module_logical_name_from_path` | `ret ptr %lN` | 0 from the transform | **12** |

`fn shape(p: text) -> text: var s = p; if s.starts_with("./"): s = s.substring(2); s`
is the **smallest fixture** that reproduces it.

The same MIR shape is **admitted under the seed's tree-walking interpreter** —
probe on a hand-built 4-block function with `Ret(Some(Copy(14)))`:
`reassigned=[14,] count=1`, `applied=true reason=ready renamed=2`,
`defs_of_14_after=0`. So the divergence is the `.unwrap()`, not the gate's logic.

### Fix (commit `be454c32040`)

All three `Ret` arms on the alloca path now use `?? MirOperand(kind:
MirOperandKind.Copy(ssa_local(-1)))` — an INVALID sentinel, so a `??` that ever
misfires still REJECTS rather than admitting an uninspected operand:
`ssa_term_operand_payloads_valid` (admission), `ssa_collect_term_operand_locals`
(cross-block-live use scan — a nil there drops the return as a use, which is
bug #2 of `llvm_constants_lost_ret_zero_2026-08-01`), and
`ssa_alloca_rewrite_term` (loads the slot back out for the `ret`).

**Still `.unwrap()`, deliberately not changed (same class, different path):**
`var_reassign_ssa.spl:425` (`ssa_rewrite_term`) and `:595`
(`ssa_replace_term_operands_for_local`) are on the phi FALLBACK path, which the
bootstrap LLVM lane never takes (`llvm_bootstrap_ssa_function` returns early
under `bootstrap_mode` when the alloca transform declines). The `CallTerminator`
arms `:289,294,297` and `:1669,1675,1681` are the same spelling on unwind-edge
destinations, unreachable by this fixture but reachable by Stage-3 code with
unwind edges.

**Not the cause, checked once:** TODOFIX-4's duplicate `rt_eprintln` LLVM
*declaration* is the emitter trailer's `unknown_func_decls` /
`bootstrap_is_runtime_declared_name` seen-set (`core_codegen.spl` trailer,
`driver_bootstrap.spl:317`), a different site from the SSA transform.

RED `3 examples, 1 failure` -> GREEN `3 examples, 0 failures`, spec
`test/01_unit/compiler/mir_opt/ssa_alloca_ret_operand_unwrap_free_spec.spl`.

## Next step for whoever picks this up

**Superseded by the section above — the knob now exists and the cause is
measured.** (Historic text kept for the mechanism it names.)
The `.ll` is deleted even with `SIMPLE_BOOTSTRAP=1` and `SIMPLE_KEEP_LLVM_IR=1`.
Located, not guessed: the guard those variables control
(`src/compiler/70.backend/backend/llvm_backend_tools.spl:242-243`) is on the
SUCCESS path, while every failure path goes through `llvm_object_stage_fail`
(`:273-281`), which calls `dir_remove(stage_dir, true)` **unconditionally** and
consults no environment variable. So on an llc error the staging dir — and with
it `module.ll` — is always removed. Making that honour `SIMPLE_KEEP_LLVM_IR` (or
emitting the module to a caller-chosen path) is step one; without the IR, line
102 cannot be attributed to a MIR instruction.

Do NOT raise `STAGE2_SELFHOST_ROUTE_TIMEOUT_SECONDS`: it is no longer even
involved — the route fails fast now.

## Closed by measurement — `build/bootstrap-boot10a`, head `be454c32040`

Full canonical run, fresh output root, `--full-bootstrap --backend=llvm --mode=dynload --jobs=10
--stop-after-stage2`, 10:41:03 -> 11:19:03 (38m00s), rc=1. Stage-2 candidate
sha256 `ba3c25f30d76c9a82a9353432be57c03…`, 152 203 632 B.

In the new candidate's own route log
(`bootstrap-boot10a/stage3/aarch64-unknown-linux-gnu/stage2-receiver.log`):

```
grep -c 'multiple definition of local value'  ->  0
```

BOOT-9's log for the same step and the same fixture carried
`module.ll:102:3: error: multiple definition of local value named 'l13'`. The llc rejection is gone.

Stage 2 sanity is still `status=pass` (`checks_run=5`, `sha_stable_status=0`,
`frontend_smoke_bootstrap_mode_status=0`); the struct-receiver step is still `status=fail`
(`probe_exit=1`, `reason=stage2-struct-receiver-failed`) and the route still exits `status 1` — but
now for a DIFFERENT and independent reason, `native-capsule-source-mutated`, filed as site 12
(`stage2_capsule_source_identity_is_sha256_of_empty_2026-09-13.md`), which was already present
underneath this one in BOOT-9's run. Stage 3/4 were correctly refused: no admitted Stage-2 parent.
