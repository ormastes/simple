# Native borrow-check verdict projection

The rejected Stage2 compiler calls `CompileContext.has_errors()` without its
receiver. Importing `CompilerDriver` pulls in the compiler closure, so this
bounded regression extracts the exact production `borrow_check` method and
uses minimal dependency models from `borrow_check_support.spl`. It verifies
the method's verdict and diagnostic accumulation, not NLL analysis or the
real context layout. The scenario body is never copied into production.

Generate a fresh projection from the current source (POSIX shell):

```sh
probe_dir=build/native_probe/borrow_check_status
mkdir -p "$probe_dir"
cp test/fixtures/native/borrow_check_status/borrow_check_support.spl "$probe_dir/"
{
    printf 'use borrow_check_support.*\n\nimpl CompilerDriver:\n'
    sed -n '/    me borrow_check() -> bool:/,/    fn format_borrow_error/p' \
        src/compiler/80.driver/driver_pipeline_passes.spl | sed '$d'
    cat test/fixtures/native/borrow_check_status/scenarios.spl
} > "$probe_dir/projection.spl"
```

Use only the parent bootstrap lane's explicitly authorized frozen producer;
this is bootstrap-only evidence, not permission to use a seed as a normal
test runner. Source the pinned `/tmp/simple-llvm23-toolchain/env.sh`, set
`borrow_authority` to the retained `stage2-runtime-authority` directory, then:

```sh
perl scripts/resource/process-tree-rss-watchdog.pl \
    --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=180 \
    --receipt="$PWD/$probe_dir/build.rss.env" -- \
    env SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 \
    SIMPLE_LIB="$PWD/src" "$borrow_authority/simple" native-build \
    --backend cranelift --runtime-bundle core-c-bootstrap \
    --runtime-path "$borrow_authority" --entry-closure --threads 2 \
    --cache-dir "$PWD/$probe_dir/cache" --mode one-binary \
    --entry "$probe_dir/projection.spl" --output "$PWD/$probe_dir/projection"
perl scripts/resource/process-tree-rss-watchdog.pl \
    --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=20 \
    --receipt="$PWD/$probe_dir/run.rss.env" -- \
    /usr/bin/time -l "$PWD/$probe_dir/projection"
```

Require native exit 0 and `borrow-check-status-pass`. Each case has a nonempty
module map. Cases cover clean completion, a prior diagnostic, a newly returned
checker diagnostic, and preserved `--no-borrow-check` behavior. Both count and
retained message checks distinguish a correct false verdict from a receiver
accident. The baseline production method fails the first case with exit 11.

For red evidence, extract the method from the recorded baseline revision
using `git show`, keeping both support and scenario files identical. Do not
restore source over concurrent work. Preserve the generated projections,
compiler/runtime identity, native artifacts, disassembly, logs, and watchdog
receipts. Full Stage2 admission must still use the actual rebuilt compiler.
