# Native reverse-reference receipt join regression

The production receipt encoder must retain its collection receiver type even
when the asynchronous free function `join` is visible. This projection imports
the real key codec and async combinator, extracts the unchanged receipt types,
validation, sorting, projection encoder and receipt encoder, and appends the
same native assertions to the baseline and corrected variants. It excludes
filesystem publication and decoding, which remain integration responsibilities.

Generate the green projection from the chosen worktree revision:

```sh
probe_dir=build/native_probe/receipt-join
mkdir -p "$probe_dir"
{
    printf 'use compiler.common.cache.reverse_reference_key.*\n'
    printf 'use std.nogc_async_mut.async.combinators.{join}\n\n'
    sed -n '/^val REVERSE_REFERENCE_RECEIPT_SCHEMA_V1/,/^fn reverse_reference_receipt_digest_v1/p' \
        src/compiler/80.driver/cache/reverse_reference_receipt.spl | sed '$d'
    printf '\n'
    cat test/fixtures/native/reverse_receipt_join/scenarios.spl
} > "$probe_dir/green.spl"
```

For red, extract that same source range using `git show
b74a4b94bbb03151b36954423798abae29c2e4c3:src/compiler/80.driver/cache/reverse_reference_receipt.spl`.
Keep imports/scenarios identical and use distinct red/green output/cache paths.
Do not substitute a local fake join: the actual async implementation makes
the wrong resolution observable as a native crash.

Use only the parent lane's frozen bootstrap-only compiler and retained LLVM23
environment. Set `probe_authority` to its `stage2-runtime-authority` directory;
require producer SHA-256
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.
For each `variant` (`red`, then `green`):

```sh
perl scripts/resource/process-tree-rss-watchdog.pl \
    --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=180 \
    --receipt="$PWD/$probe_dir/$variant-build.rss.env" -- /usr/bin/time -l \
    env SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 \
    SIMPLE_LIB="$PWD/src" "$probe_authority/simple" native-build \
    --backend cranelift --runtime-bundle core-c-bootstrap \
    --runtime-path "$probe_authority" --entry-closure --threads 2 \
    --cache-dir "$PWD/$probe_dir/cache-$variant" --mode one-binary \
    --entry "$probe_dir/$variant.spl" --output "$PWD/$probe_dir/$variant"
perl scripts/resource/process-tree-rss-watchdog.pl \
    --max-rss-kib=5859375 --interval-ms=100 --timeout-seconds=20 \
    --receipt="$PWD/$probe_dir/$variant-run.rss.env" -- \
    /usr/bin/time -l "$PWD/$probe_dir/$variant"
```

Both builds must succeed without stubs. Baseline exits139; corrected binary
must print `reverse-receipt-join-pass` and exit0. Assertions compare exact
empty/populated/duplicate frames (including sort order and no trailing
newline), and reject unsupported schema, empty/newline owner, carriage-return
root, empty consumer and invalid key. Retain logs, hashes and RSS receipts.
This bootstrap-only projection is not an admitted compiler-test matrix result.
