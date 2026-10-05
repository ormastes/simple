# Text ordering parity in native runtime arrays

Backport source: `92256293b90cb577f53d3222dfb6ddb660ba914b`. Isolated release base: `09b75827ffa40e7cb25a81b4730faf8319442ad3`.

The C `rt_array_sorted` comparator and Rust shared sort comparator previously treated every text pair as equal. Consequently a native/JIT sorted text array could preserve unsorted input while the interpreter ordered it, potentially producing different environment-row digests. Add only the text/text arm: compare bytes, then length for equal prefixes. The existing string type checks are present on this release; no upstream compiler, write_span or provider prerequisites are needed. Other pairwise comparisons retain their prior semantics.

C in-place `rt_array_sort` already uses the separate text-aware `rt_sort` owner and needs no implementation change. Rust in-place ascending, descending and copied sorting share the repaired comparator. This patch does not introduce a total ordering for arbitrary heterogeneous arrays: existing equal cross-type pairs can be nontransitive. Tests check individual mixed pairs and existing numeric precedence rather than claiming global heterogeneous ordering.

## Focused regressions

`src/runtime/test/text_sort_selfcheck.c` calls real public C allocation, string, array and sort APIs. Before: exit1, check11, first expected empty text remains unsorted. After: exit0,95 checks. Coverage includes ASCII case, prefixes, UTF8/astral text, empty text, embedded NUL, copied-sort input preservation, existing in-place sorting, eight text/nontext ordered pairs and integer-before-float precedence.

Artifacts: `/var/tmp/item5-text-sort-parity-20261006/{before,after,before.log,after.log}`. The native recipe uses production `runtime_native.c`, Clang `-std=gnu11 -O1 -ffunction-sections -fdata-sections -DSIMPLE_CORE_C_STANDALONE=1 -Isrc/runtime`, then links the selfcheck with `-Wl,--gc-sections -lpthread -ldl -lm`. Original baseline source is retained as `before.c`. Private driver recipe: `D:/dev/simple/build/review/item5-text-sort-proof.sh`.

Rust regression source retains the two upstream text cases, extends bytewise input with embedded NUL and astral UTF8, and adds mixed-pair preservation. Exact bounded test invocation from `src/compiler_rust`:

```
cargo test --locked --offline --manifest-path Cargo.toml --target x86_64-unknown-linux-gnu -p simple-runtime test_array_sort --lib
```

Fresh private Cargo home/target/tmp are under the evidence directory; one build job,900-second wall limit and2,000,000KiB enforced RSS cap. No existing bootstrap cache or runtime authority is written. First orchestration attempt could not locate Cargo before compilation; the corrected invocation uses `/root/.cargo/bin` on PATH and does not rerun the green native C criterion.

Rust actual test binary: exit0,7 passed,0 failed,1333 filtered. This includes the three focused text/mixed tests and existing numeric ascending/descending/invalid-sort cases. Log: `/var/tmp/item5-text-sort-parity-20261006/rust.log`; enforced receipt: `/var/tmp/item5-text-sort-rust-proof.rss.env`. No compiler/Simple application, end-to-end daemon routing or performance qualification is claimed. Native and Rust byte-order parity is the intended scope.
Reproduce the native criterion from repository root (under the normal process watchdog):

```
clang -std=gnu11 -O1 -ffunction-sections -fdata-sections -DSIMPLE_CORE_C_STANDALONE=1 -Isrc/runtime src/runtime/test/text_sort_selfcheck.c src/runtime/runtime_native.c -Wl,--gc-sections -lpthread -ldl -lm -o /tmp/text-sort-selfcheck
/tmp/text-sort-selfcheck
```

Frozen tested sources (SHA256):
- C owner: `3e0fc373eddd4cbc6bbea51a4c1448eb0b4a081a0018c274af8e2ed4eb5b56c5`
- C oracle: `26214a04aafc99b1b1cff2e1c0a48a0a014b87401dba3e146f35d5b523b90b4b`
- Rust owner: `69490dc7e7d1255c341c680949fba05ef19b0ba2471dd129f048773a61439327`
- Rust tests: `711838f118a41d8fe1849111aa4f26a31229a1f492b300c88e70fe43e7ce0f9a`

Independent source review found no P0/P1. The upstream private byte helper has an unconstrained borrow lifetime; its current use immediately compares live array elements without mutation or escaping references. This patch does not broaden that helper's visibility or use.