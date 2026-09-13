# Site 12: the Stage-2 candidate freezes every native capsule's source identity as sha256("")

- **Status:** OPEN (2026-09-13)
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

Two candidate causes, not yet separated:

1. **A native-codegen struct-field-binding defect** — the same class this tree
   already documents at `driver_aot_native_output.spl:855-872`, where a
   match-bound `case Ok(source): sha256_text(source.content)` read field 0
   (`path`) instead of `content` on a Stage-2-compiled compiler and produced the
   digest of the PATH STRING. Supporting evidence from the same runs: the
   candidate's own canary fires —
   `[receipt-size-canary] optional-bound scalar field read miscompiled: field=907999041:runtime=1592`
   (`driver_aot_native_output.spl:989`), i.e. an optional-bound `fp.size` read
   returned 907999041 where the real object size is 1592.
2. **Ordering against `SIMPLE_STAGE3_STREAMING_SURFACES=1`** — the gate sets it,
   and the build log shows `phase2:surface:file:released path=…` for every file
   before the capsule batch is frozen, so `source.content` could be legitimately
   empty by then.

Cause 1 is the better-supported of the two (the canary is the candidate
reporting a field read it knows is wrong, in the same file), but neither has
been isolated with a one-variable run; the discriminator would be a build with
`SIMPLE_STAGE3_STREAMING_SURFACES=0`, which this lane did not run because the
files are fenced.

## Repro

```sh
sh scratchpad/boot10/fxrun.sh scratchpad/boot10/fx/f1.spl f1
grep -A1 native-capsule-source-mutated scratchpad/boot10/fxrun/f1/build.log
```

Raw evidence: `scratchpad/boot10/fxrun/*/build.log`, `scratchpad/boot10/route11c.log`,
and BOOT-9's `stage2-receiver.log` quoted above.
