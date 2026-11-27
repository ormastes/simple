# Nativeall path component exports missing

Status: **P1/open; fix implemented, verification pending**. Root canonical claim remains fixing under `01a1afac/nativeall-path-components`; not resolved. Base `bfcab1cde567ad9efa4ced3bb2c67299587dde14`.

The retained nativeall linker cannot resolve `rt_path_filename` and `rt_path_extension`. The C owner runtime_native.c15101-15124 and Pure-Simple boxed-text ABI slots text_extern_abi.spl356 establish RuntimeValue-to-RuntimeValue boundaries. The Rust path owner now implements precisely these two exports, without C private layout or platform Path aliases.

Both scan counted UTF-8 bytes, trim trailing forward slashes, and select the basename or last-dot extension within that basename. Only '/' separates components; backslash and NUL remain ordinary bytes. A lone leading dot does not start an extension. There is no 4096-byte limit. Invalid/wrong-kind/unsupported UTF-8 input returns empty managed text. A fallible Vec reserve copies only the selected suffix under with_typed_ptr; its registry guard ends before the real Rust string constructor allocates the result. Other path APIs are unchanged.

## Evidence and limits

Exactly **2/6 cycles**: attempt1 failed before tests because counterpart_abi_runtime.c25 needed the missing tools/counterpart SDK header; attempt2 restored only11 missing pinned inputs after comparison against all3544 proven mtime inputs and passed all6 selected tests. No source retry, automatic third retry, green rerun or quota increase.

Actual filter `value::sffi::file_io::path::path_component_tests::`, `--test-threads=1`, offline locked default cpu-simd Windows gnullvm bootstrap runtime tests: **6 passed, 0 failed, 1414 filtered**; compile2m07s. Cases: filename lexical, extension lexical, counted NUL and long paths, invalid values and UTF-8, snapshot surviving input release, result surviving input release. Cached short strings may share identity; tests do not require pointer uniqueness.

Tested raw SHA256 production `6d972606a2bed01346ecca0ae5fa18ff102377a526c8bdb0e2c749625fd9994c`; tests `10809b2741d8e41f07662bd6cabb92e6b34ca3e3ee42dcc8dc1a42584ca19722`. Materialization preserved these exact bytes; root .gitattributes changes Git filtered identity only. Final filtered blobs recorded in host evidence.

Guard SHA256 `2ea4a7b7488fb7693080d26388c21a3e17b2961bb891da9d0f4cabc020e03a03` is the root-reviewed one-line TARGET_LIMIT_BYTES3GiB-to1GiB copy; old3c72 guard unchanged. Windows Job enforces8GiB memory,2CPU affinity and process-tree containment. RSS8GiB, target1GiB and disk2GiB reserve are sampled soft monitoring bounds, not instantaneous OS quotas. Timeout1200s/log32MiB unchanged. Attempt2 child0/resource_errornone; committedpeak1277718528, RSS1172819968, target279433216 bytes. Log SHA256 `7031a88279bd4dcd53f5238d736dc8140267c1c35a1506cbe9b73c92b58fc046`.

Exact command/env/source/log/receipt files: `C:/dev/simple/.git/worktrees/nativeall-path-components-d88f/evidence/runtime-owner-attempt{1,2}.*`. Restored inputs: attempt2-input-repair.json. No cache hardlinks or shared writes.

Unsafe inventory remains **FAIL400/399 variants and3764/3546 migration**; reused, not rerun or waived. Exact44954 owned SPL map SHA256 `a63e8ab8b722dbc4853a0f5d88b2a87f44e35e24f591c2b1a2ce29729ed524ca`, audit scripts blobs `3b73712b805b979280f7eb1f0c09f9d941d1114e` and `394b158d0514cb2a6f94a6b46def4791cc815da6`; reference stdio evidence/stdio-unsafe-input-equality.sdn and rebase-input-equality.sdn. This branch changes two Rust files and tracking only; source-only SPL warning inventory excludes the Rust boundary.

Nativeall link, P2 self-hosted native behavior, SSpec, full core/MCP verification: **UNRUN**. Runtime-owner Cargo tests are not native acceptance. Draft PR only, not ready/merged/closed. Provider input/output/cache-read/cache-create tokens=unavailable; comparable cohort average=unavailable; ratio=unavailable.

## Draft update cycle4

Rebased onto checker fix `c4b6e0c0dbeef6c4b8bd45a9b3d958deca25e7de`. Cycle3 server ratchet falsely counted the six #[test] names as runtime primitives; shared checker repair landed independently. No test renames or Rust changes. Tested raw and normalized Git blobs preserved. Runtime Rust/Cargo/build definitions unchanged; the two changed core C translation units are absent from runtime build literal source roots and their quoted-include closure (same build owner used by native-all-provider). This is scoped compile dependency evidence, not full runtime-input equality: those C files did change. No owner rerun; broad verification stays UNRUN. Exact44954SPL/two audit-script input proof remains unchanged; no audit rerun. Conservative cycle4of6.
