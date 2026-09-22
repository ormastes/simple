# Native cache witness receiver projection

This fixture tests the production witness call and production witness logic.
It extracts the real fact-set structure/method into a small support module;
only the fact producer is replaced. It does not exercise the complete driver,
resolver, retained surfaces, or native-cache admission.

Generate the projection from the selected source revision:

```sh
probe_dir=build/native_probe/native-cache
fixture_dir=test/fixtures/native/native_cache_receiver
mkdir -p "$probe_dir"
{
    printf 'use compiler.driver.cache.action_key.{ActionDep}\n'
    printf 'use compiler.driver.cache.native_module_witness.*\n\n'
    sed -n '/^struct NativeModuleCacheFactSetV1:/,/^fn native_module_cache_fact_set_invalid_v1/p' \
        src/compiler/80.driver/cache/native_module_witness_facts.spl | sed '$d'
    cat "$fixture_dir/support_tail.spl"
} > "$probe_dir/fact_support.spl"
{
    cat "$fixture_dir/projection_prefix.spl"
    sed -n '/    val witness = /,/    if not witness.valid:/p' \
        src/compiler/80.driver/driver_aot_native_output.spl | sed '$d'
    printf '    witness\n\n'
    cat "$fixture_dir/scenarios.spl"
} > "$probe_dir/projection.spl"
```

For red evidence, extract the call from baseline `396934b0ec49` with `git show`;
keep support/scenarios identical and use distinct red/green entry/output/cache
paths. Both variants import the unchanged real witness, canonical encoders,
and SHA-256 implementations. Baseline exits 139; fixed prints
`native-cache-receiver-pass` and exits zero.

Use only the parent lane's explicitly authorized frozen bootstrap producer.
This is bootstrap-only evidence, never a general seed-based test-runner pass.
Source the retained LLVM 23 environment and set `probe_authority` to the
frozen `stage2-runtime-authority` directory:

```sh
perl scripts/resource/process-tree-rss-watchdog.pl \
    --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=180 \
    --receipt="$PWD/$probe_dir/build.rss.env" -- /usr/bin/time -l \
    env SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 \
    SIMPLE_LIB="$PWD/src" "$probe_authority/simple" native-build \
    --backend cranelift --runtime-bundle core-c-bootstrap \
    --runtime-path "$probe_authority" --entry-closure --threads 2 \
    --cache-dir "$PWD/$probe_dir/cache" --mode one-binary \
    --entry "$probe_dir/projection.spl" --output "$PWD/$probe_dir/projection"
perl scripts/resource/process-tree-rss-watchdog.pl \
    --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=20 \
    --receipt="$PWD/$probe_dir/run.rss.env" -- \
    /usr/bin/time -l "$PWD/$probe_dir/projection"
```

Require both bounded receipts and real output. The scenarios cover empty and
populated dependency arrays, module/MIR identity, dependency-fold changes,
agreement with direct witness construction, and retained rejection reasons
for missing module identity and malformed dependency facts. Resolution/layout
arrays are empty here; their nonempty production behavior remains outside
this projection. Full rebuilt Stage2 admission remains the integration gate.
