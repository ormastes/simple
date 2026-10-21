# Configured HTTP clients lacked a native default-header provider

Review of `4edc71d0da6` found that extracting the configured-client owner
preserved a pre-existing undefined `rt_http_client_set_header` symbol. The
native runtime implemented create, timeout, request and destroy, but not the
header setter. Moving its declaration did not establish provider completeness.

The repair adds that existing ABI to its canonical native client-slot owner.
Defaults are owned copies bounded to 1,024 fields and 1 MiB per live client.
Setting a name replaces its prior value case-insensitively; token names,
control-free values, generation identity, and limits are checked before commit.
Allocation failures preserve existing state. Destruction frees all defaults.

Requests snapshot defaults and timeout while holding the existing slot lock.
Explicit request fields override defaults case-insensitively. The combined
header budget is checked before transport. The lock is released before I/O;
copied snapshot strings and their array are released afterward. Clients without
defaults keep the original direct transport route without snapshot allocation.

## Boundary choice

The SFFI selection skill and repository wiki were read; no existing native
setter provider was found. A pure Simple field on `HttpClient` would not persist
through the existing value-argument setter API. A Simple global registry would
also need interception of existing raw request/destroy ABIs, and cannot safely
fix just the typed setter while leaving raw callers with different behavior.
The parent explicitly authorized the smallest native slot-owned state repair.
No application platform branch or new foreign library was introduced.

## Executed evidence and limits

MinGW GCC 15.2.0 compiled the actual `runtime_native.c` through
`test/harness/http_client_headers_c_harness.c`:

```text
gcc -std=c11 -O1 -ffunction-sections -fdata-sections -Wl,--gc-sections
  test/harness/http_client_headers_c_harness.c
  test/harness/rt_clear_harness_stubs.c
  -o build/http-header-boundary/http_client_headers.exe
  -lws2_32 -lbcrypt -lole32 -luuid -luser32 -lgdi32
HTTP configured headers: 21 checks, 0 failures
```

The harness checks copied input lifetime, replacement, injection rejection,
invalid request headers, cleanup, stale generations, count/byte bounds,
request override at capacity, and combined-header overflow. Unrelated runtime
link dependencies use existing fail-fast harness stubs plus three equally
fail-fast platform link stubs; no HTTP/client operation is stubbed. This is
native boundary evidence, not a Simple compiler, product, or live HTTP result.

Windows `rt_http_get`, request, request-v2 and download still explicitly return
`native HTTP is unavailable on Windows core runtime`. Completing that transport
is deferred by the user's narrowed bootstrap-through-Phase3 scope. The Simple
nine-check configured-client live echo probe remains pending a usable producer
and real transport. No self-hosted or Phase3 admission is claimed by this fix.

## Canonical MSVC compile and inventory baseline

The changed runtime was also compiled, without linking or executing a Simple
compiler, by canonical LLVM 23.1.1 `clang-cl` using the sourced
`scripts/setup/windows-msvc-bootstrap-env.shs` environment (Visual Studio
14.44.35207 and Windows SDK 10.0.26100). Flags were `/std:c11 /c
/DSIMPLE_ABI_VERSION=1 /DSIMPLE_ABI_VERSION_DEFERRED=0`. Compilation exited 0,
producing `build/http-header-boundary/runtime_native-msvc.obj` (484,155 bytes).
There were 51 compiler warnings; this is compile evidence, not a warning-free
claim or product admission.

The mandatory source SFFI backlog audit failed its inventory ratchet. To
attribute that failure, the same deterministic source-only inventory ran on
two explicit LF-delimited source lists. The baseline restores every modified
preexisting Simple source from `git show 380200890ff:<path>` in a private
overlay and excludes the two new Simple sources. All other source bytes are
shared unchanged with the current tree. The two lists contain 41,568 and
41,570 files respectively. Source inventory TSVs are retained privately under
`build/http-header-boundary/baseline/retry-*` and `current-retry-*`.

Both baseline and `57b80b6fbf7` produce the same failing thresholds:

```text
source_variants=407/399 migration=3612/3546
symbols=4320 unique(symbol, source_signature)=4863
signature-identity set delta=0
```

The only aggregate symbol-row delta is the configured-client probe's extra
`sys_get_args` declaration: declarations 34 to 35, contract-missing declarations
30 to 31. Its two distinct signatures, 26 missing unsafe tags, and migration
classification are unchanged. Thus neither threshold excess was introduced by
the HTTP repair. This does not waive the failing repository-wide gate; no
threshold or governed manifest was relaxed.

The added probe's argv annotation was subsequently given its actual native
contract: a fresh runtime-layout text array, with nil denoting allocation
failure. A focused inventory containing only that probe exited 0 and classified
`sys_get_args` as `unsafe_tag=tagged`, `contract=documented`, and
`state=unsafe_contract_declared`. This resolves the new declaration's missing
contract without changing its ABI or relaxing thresholds. The paired full
inventories above remain the preserved pre-annotation comparison; no repeated
whole-tree inventory was used to claim an updated full-tree PASS.
