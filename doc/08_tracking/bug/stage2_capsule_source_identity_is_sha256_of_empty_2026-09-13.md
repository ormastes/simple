# Site 12: the Stage-2 candidate freezes every native capsule's source identity as sha256("")

- **Status:** OPEN (2026-09-13) — cause ISOLATED to `SIMPLE_STAGE3_STREAMING_SURFACES=1`, fix blocked (fenced files)
- **Lane:** BOOT-10, measured on the pinned Stage-2 candidate
  `build/bootstrap-boot9b/stage2-rejected/aarch64-unknown-linux-gnu/simple`,
  sha256 `99ba0cf430d255a4141edfc7…`, 152198272 B (pin
  `scratchpad/boot9/pin/cand.boot9b.stage2`).
- **Severity:** a SECOND, independent Stage-2 admission blocker. It fails a
  native-build unit whose IR is perfectly valid, so fixing site 11
  (`stage2_route_llvm_ir_duplicate_local_name_2026-09-13.md`) alone does not
  admit Stage 2.
- **Fenced:** the two implicated files are on `scratchpad/egl_offlimits_v2.txt`
  (`src/compiler/80.driver/driver_types.spl`,
  `src/compiler/80.driver/driver_aot_native_output.spl`), so this lane measured
  and filed it rather than fixing it.

## It is already live in the real bootstrap, not just in a standalone repro

`build/bootstrap-boot9b/stage3/aarch64-unknown-linux-gnu/stage2-receiver.log`
(BOOT-9's canonical `--stop-after-stage2` run) reports **two** failing units,
and only one of them is site 11:

```
line  8: error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
line 69: native-capsule-source-mutated
line 70: cache-source=scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl
         capsule-identity=e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
         disk-identity=404569fc2e1d74f7b292c14b75766e041dfc84c45cc409899c8255796651bc45
line 73: llc: …/module.ll:102:3: error: multiple definition of local value named 'l13'
line 96: build failed: 2 failed, 0 unverified, 0 not run, 0 ok of 2 unit(s)
```

`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` is
**sha256 of the empty string**. The cache scope directory is named from the same
digest (`se3b0c44298fc1c149afbf4c8996fb924`), and the object receipt left in
BOOT-9's tree sits under that directory
(`…/native-build/v1/se3b0c44298fc1c149afbf4c8996fb924/object.….hello_world.o.capsule-receipt`),
so the emptiness is not specific to one module.

## Same digest for every source, including ones whose IR is clean

Reproduced standalone with the gate's own env (`scratchpad/boot10/fxrun.sh`):

| fixture | duplicate `%lN` | llc | capsule-identity | disk-identity |
|---|---|---|---|---|
| `f1.spl` (4 lines, reassign in `main`) | 0 | accepted | `e3b0c442…` (sha256 "") | `7dfe1e7b…` |
| `f2.spl` (while-loop reassign in `main`) | 0 | accepted | `e3b0c442…` | (differs) |
| the gate fixture `stage2_module_path_naming.spl` | 12 | rejected | `e3b0c442…` | `404569fc…` |

f1 and f2 produce **valid IR that llc accepts** and still exit 1 with
`native-capsule-source-mutated`. So this is not a side effect of site 11.

## Where it is computed

`FrozenNativeModuleCapsuleBatchV1`'s `source_identity` comes from
`frozen_native_cache_source_identity_v1` (`driver_types.spl:1055-1062`):

```
for source in self.sources:
    if source.module_name == module_name:
        found_identity = sha256_text(source.content)
```

`sha256_text("")` is exactly the observed digest, so `source.content` reads
empty in the candidate. The check that fires is
`driver_native_collect_capsule_result_v1`
(`driver_aot_native_output.spl:1078-1083`), comparing it against
`driver_native_disk_source_identity`, which reads the file directly and is
correct.

## CAUSE ISOLATED (2026-09-13) — `SIMPLE_STAGE3_STREAMING_SURFACES=1`

One variable, same candidate (`ba3c25f30d76c9a8…`, the Stage-2 binary from
`build/bootstrap-boot10a`), same fixture `f1.spl`, everything else identical:

| `SIMPLE_STAGE3_STREAMING_SURFACES` | `native-capsule-source-mutated` lines | outcome |
|---|---|---|
| **1** (what the gate sets) | **3** | `build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s)` |
| **0** | **0** | `phase=link state=succeeded … succeeded=1`, binary linked |

So it is an **ordering defect, not a codegen field-binding defect**: streaming
surfaces release each file's text (`phase2:surface:file:released path=…`) before
`freeze_native_module_capsules_v1` runs, so `frozen_native_cache_source_identity_v1`
(`driver_types.spl:1055`) hashes an already-released `source.content` and gets
`sha256("")`. The identity must be captured while the surface is still held (or
read from disk, as `driver_native_disk_source_identity` already does), not at
freeze time.

**Explicitly NOT the cause, though it looked like one:** the candidate's
`[receipt-size-canary] optional-bound scalar field read miscompiled` line fires in
BOTH legs — 3 times with streaming OFF (`field=742848097:runtime=1256`), where the
build SUCCEEDS. It is a real, separate miscompile of an optional-bound `fp.size`
read (`driver_aot_native_output.spl:989`) and is worth its own record, but it does
not produce the empty capsule identity.

Reproduce the split with `BOOT10_STREAM=0` / `BOOT10_STREAM=1`:
```sh
CAND=scratchpad/boot10/pin/cand.boot10a.stage2 BOOT10_STREAM=0 \
  sh scratchpad/boot10/fxrun.sh scratchpad/boot10/fx/f1.spl f1stream0
```

## Repro

```sh
sh scratchpad/boot10/fxrun.sh scratchpad/boot10/fx/f1.spl f1
grep -A1 native-capsule-source-mutated scratchpad/boot10/fxrun/f1/build.log
```

Raw evidence: `scratchpad/boot10/fxrun/*/build.log`, `scratchpad/boot10/route11c.log`,
and BOOT-9's `stage2-receiver.log` quoted above.

## Confirmed as the SOLE remaining blocker (2026-09-13, BOOT-10)

With site 11 fixed (`be454c32040`), the canonical `--stop-after-stage2` run
`build/bootstrap-boot10a` (head `be454c32040`, Stage-2 candidate
`ba3c25f30d76c9a82a9353432be57c03…`) shows **zero** llc errors in the route log and both units
failing here instead:

```
| error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
| error: native capsule collection failed -- module, tag and detail follow
cache-source=src/compiler/common/module_path_naming.spl
  capsule-identity=e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
  disk-identity=c84a1cf364dcf48b5ec6bec5e8ecf7ecb07411c9089b4620b8b92d5f76a09c95
cache-source=scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl
  capsule-identity=e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
  disk-identity=404569fc2e1d74f7b292c14b75766e041dfc84c45cc409899c8255796651bc45
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Same sha256("") identity for two different sources on a freshly built compiler, so this is
reproducible across candidates and is what blocks Stage-2 admission now.
