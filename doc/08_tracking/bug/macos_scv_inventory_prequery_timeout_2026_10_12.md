# macOS native-build pre-query SCV timeout

Status: OPEN; bounded native startup observation, underlying cost cause unknown.

Rejected immutable404042 candidate/frozen5e source: diagnostic cycle1 host_arch breakpoint resolved but external120s timeout beforehit. Cycle2 asynchronous70s interrupt proves stack calloc→rt_array_new→compile_source_inventory_encode_v1→compile_source_inventory_decode_content_v1→scv_compile_snapshot_inventory_entries_v1→snapshot_acquire→compiler_source_authority_acquire→native_build_worker. No process tuple or host_arch evidence reached. Native shell uname-m status0/arm64 independently confirmed.

Frozen5e and inspected currentrelease inventorycore/decode owners are byteidentical. Sorted input validation is linear, fallback heap-sortO(nlogn); encoder builds7field rows then joins once. Decode parsesentries then canonicalreencodes. Allocation count/size, actual inventoryentrycount/bytes andRSS unknown; calloc stack is not proof of a memory bug or asymptotic regression. Artifact contains no SCVinventory and only152B one-line incrementalmanifest.

Evidence /mnt/c/Temp/simple-macos-hostarch-diagnostic-20261012/native-cycle2/boundary.json. No source repair and no unchangedthirdretry. Future diagnostic must preserve actual sourceauthority and separately qualify any tagged minimalGitfixture input.

## Tagged diagnostic projection

WORKAROUND_MAC_HOSTQUERY_FINITE_SOURCE_PROJECTION: copy exact frozen p2_add bytes/path into fresh Git one-file fixture; cmp andSHA receipt required. Explicit supported --source src/compiler/bootstrap_admission narrows snapshot selection. Immutable frozen stdlib remains SIMPLE_LIB authority. Original full-source inventory/cache untouched; separate minimalcache. This probes host-query ABI only, excludes full compiler admission and bootstrap PASS. Same rejected404042 bytes/tool/runtime remain; cycle3 final boundeddiagnostic authorized only after source review.
