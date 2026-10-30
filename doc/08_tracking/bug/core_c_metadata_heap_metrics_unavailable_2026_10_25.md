# Core-C metadata fixture cannot use the Rust live-heap metric contract

Status: actual instrumentation gap; no runtime fix claimed. Source base
`39af391381dfa8f8b54467655a96e5eadd74afda`. This is separate from the scoped
source-authority repair (source cycle 2, native comparison 3 prepared).

The immutable 5a6 bootstrap diagnostic built the 154-module baseline with native
exit 0. Its actual link command selected a temporary
`core_c_runtime/simple_runtime.lib`, not Rust-nativeall058. The temporary archive
was cleaned, so its bytes and member definitions cannot now be independently
hashed. No output runtime DLL exists. The retained link command/profile is
evidence of selection, not a claim of identical archive bytes or Rust ownership.

The baseline ran all 535 real inventory/manifest and scope-lifetime assertions
successfully: native exit 0, quiescent, 1.875 s, guard peak 563,656 KiB. Its
selected-runtime observations were header live bytes 0 throughout and auxiliary
live/array-capacity values both constantly 3. Those values cannot establish
live metadata retention. The measurement guard stopped before the scoped build.
All failure evidence remains immutable under
`C:/dev/simple-source-authority-validation-ab-storage-20261025/evidence-core-c-continuation/first-boundary.sdn`.

Concrete source/evidence boundaries:

- `runtime_memtrack.c` initializes `g_memtrack_enabled` and `g_live_bytes` to 0.
  The Windows fallback `rt_heap_live_bytes` returns that C tracker total. This
  differs from Rust `value/heap.rs`'s registered heap-header accounting, so the
  same symbol name does not establish the same observation domain.
- No C definitions of `rt_heap_aux_live_bytes` or
  `rt_heap_array_capacity_bytes` were found in the owned runtime. Both symbols
  occur in the actual build log's `Unresolved symbol preview` (line 189).
  The seed's `native_project/stubs.rs` emits tagged-nil sentinel 3 fallback
  bodies for unresolved optional symbols. That source route and the observed
  constant 3 values support an inference of fabricated fallback counters;
  there is no retained symbol-provider map proving their individual addresses.
- Actual RSS observations were 4,844 KiB before validation, 412,612 KiB after
  24 validations, and 532,108 KiB at the end. These are separate observations,
  not substitutes for a missing allocator counter or proof of Rust-parent
  savings.

Required future repair: expose a provider-aware availability/domain contract
and real Core-C allocation accounting, or reject unsupported metric calls before
they become sentinel-valued observations. Do not interpret zero/3 as successful
live-heap measurement. No such runtime change or extra build is authorized here.

The next finite experiment keeps the patch and 535-check fixture unchanged,
reuses the successful baseline build/run, and executes only scoped build/run
under the same observed C profile, inputs, tools, 24 requested jobs and
5,859,375 KiB limit. Report correctness separately; leave heap retention UNMET
and compare only measured after-24-minus-before RSS, guard peak and elapsed
time. An empirical C-profile RSS reduction does not qualify the full compiler,
prove archive byte identity, guarantee RSS release, or prove Rust058 coordinator
headroom.
