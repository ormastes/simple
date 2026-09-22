# Native capsule identity transport projection

Status: native PASS in the explicit-self containment lane (2026-09-23).
This is bootstrap-only evidence, not Stage2 admission or compiler-suite PASS.

The two-module fixture uses actual capsule classes, freeze implementation,
uncached production call, and input validator. Context source/storage providers
and MIR/storage serialization are modeled. It checks argument transport and
identity validation, not filesystem mutation, real MIR serialization, or full
compiler behavior. Explicit-self context stubs preserve instance-method arity
even where their modeled bodies do not need context state.

Assemble `capsule_support.spl` in this order:

1. `support_prefix.spl`.
2. Production `src/compiler/80.driver/driver_types.spl` from
   `class FrozenStorageModuleSnapshotV1:` to before `extern fn rt_string_free`.
3. `context_prefix.spl`.
4. Production method from `    fn freeze_native_module_capsules_v1(` to before
   `    me add_error(`, retaining indentation inside the fixture context.
5. Production `src/compiler/80.driver/driver_aot_native_output.spl` function from
   `pub fn driver_native_capsule_inputs_valid_v1(` to before
   `fn driver_native_leading_spaces(`.
6. `export MirModule, CompileContext, FrozenNativeModuleCapsuleV1, FrozenNativeModuleCapsuleBatchV1, driver_native_capsule_inputs_valid_v1, FrozenNativeCapsuleConfigV1`.

Assemble `projection.spl` from `projection_prefix.spl`, the exact production
call from `            val capsules = ctx.freeze_native_module_capsules_v1(uncached_names,`
to before `            if not capsules.ok:` (remove eight leading spaces),
then `    capsules`, a blank line, and `scenarios.spl`.

Green uses production source verbatim. Red is the same projection with only
`self, ` removed before `module_names: [text]` in the freeze signature. It
isolates the imported receiver metadata defect; it does not separately prove
the scalar config contraction is necessary. The earlier rejected production
binary provides the eleven-argument truncation evidence.

Set `probe_variant` to the absolute red/green directory and `probe_authority`
to the frozen bootstrap authority recorded in the linked report. Source the
parent evidence `llvm23-env.sh`, then build and run separately:

```sh
perl scripts/resource/process-tree-rss-watchdog.pl \
  --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=180 \
  --receipt="$probe_variant/build.rss.env" -- /usr/bin/time -l \
  env SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 \
  SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 \
  SIMPLE_LIB="$PWD/src" "$probe_authority/simple" native-build \
  --backend cranelift --runtime-bundle core-c-bootstrap \
  --runtime-path "$probe_authority" --entry-closure --threads 2 \
  --cache-dir "$probe_variant/cache" --mode one-binary \
  --entry "$probe_variant/projection.spl" --output "$probe_variant/projection"
perl scripts/resource/process-tree-rss-watchdog.pl \
  --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=20 \
  --receipt="$probe_variant/run.rss.env" -- \
  /usr/bin/time -l "$probe_variant/projection"
```

Require exit 0 plus `capsule-identity-transport-pass` on green, a nonzero red
exit, and bounded receipts with quiescent cleanup. Scenarios check exact
canonical identity (not just equality of two potentially nil values),
nonempty provider receipt, both witness maps, explicit empty built-in values,
option mismatches, provider admission, and rejection after every modeled
identity input is mutated. Restoring valid inputs restores acceptance.
Omitted-default argument lowering and batch find are not executed here.

Evidence and limits:
`doc/08_tracking/bug/stage2_capsule_explicit_receiver_containment_2026-09-23.md`.
