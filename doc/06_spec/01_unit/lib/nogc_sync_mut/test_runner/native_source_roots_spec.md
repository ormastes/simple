# Native SSpec ordered source roots

**Status: authored manual; execution and docgen pending (TEST_BLOCKED).**
Source: `test/01_unit/lib/nogc_sync_mut/test_runner/native_source_roots_spec.spl`.
Requirement: **REQ-NATIVE-TEST-SOURCE-001**, traced in all ten unexecuted cases.

The production parser accepts repeatable `--native-source PATH` and
`--native-source=PATH`, retaining up to five existing directory roots in order.
Roots select Native execution, LLVM unless another backend was selected, no
result cache reuse, actual-execution assertions and no unbound daemon/session
sharing. Native compilation still requires a pinned producer.

1. Validate real checkout roots and parse both spellings. Provider precedence
   and the original spec path survive as actual array values.
2. Select roots alone. LLVM AOT, no cache reuse, execution assertions and
   disabled daemon/session sharing override conflicting earlier mode requests.
3. Retain an explicit Cranelift backend; empty-root legacy compile behavior
   remains unchanged.
4. Refuse missing, empty, absent-directory and file-valued source roots through
   the existing argument validator.
5. Accept five real roots and refuse the sixth instead of discarding it.
6. Refuse control characters, manually constructed unqualified native requests
   and unsafe mode combinations before compiler launch.
7. Generate exact native-build argv with each ordered `--source` selector
   before the entry. Recover the same root values from that actual argv.
8. Generate worker arguments and parse their child options. Root order and
   native execution policy survive the process boundary contract.
9. Reverse identical roots. Their length-framed identity and invocation receipt
   differ, preserving resolver precedence in cache/provenance selection.
10. Read the same values through existing configured GC and async facades.
    These explicit test imports verify current delegates; production configured
    family selection is unchanged.

The canonical implementation remains under `nogc_sync_mut/test_runner`.
`nogc_async_mut` delegates there, `gc_async_mut` delegates through the async
facade, and `gc_sync_mut` delegates through the GC facade. No generic import was
globally pinned. The unused app-local parser/executor copies are not the native
execution owner. Source changes do not qualify older producer generations.

The spec calls production parser, real directory validation, compile arguments,
worker argument construction and receipt identity. It launches no compiler,
worker or test binary. Actual configured native imports, fresh/warm backend
execution, cache invalidation, generated manuals and required core/MCP smoke
checks remain blocked pending an admitted source-matched runtime.

After admission, execute this spec with LLVM and Cranelift, record exact
producer/provider/source/cache identities and actual cases, then generate its
mirrored manual with zero stubs and run `sspec-maintain scan`. No execution or
docgen pass is claimed here.
