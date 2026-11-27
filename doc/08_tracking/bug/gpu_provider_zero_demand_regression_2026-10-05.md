# GPU provider zero-demand and repeated-demand regression

Status: focused Linux native loader regression passed; no production defect
was observed or production owner changed.

The selected item 5 acceptance cases I5-01/I5-02 require inert registration
and loading on first capability demand. The existing registry check exercised
load, ABI rejection, missing/incomplete providers, replacement and concurrent
access, but did not observe a provider constructor before first demand.
Calling `rt_gpu_provider_loaded` or the ABI getters cannot fill that gap:
those production APIs intentionally demand loading.

`scripts/check/check-gpu-provider-dynload-registry.shs` now equips its existing
shared-library fixture with constructor/destructor markers in an external
file. The marker environment is set before process startup, so the independent
file observer also detects a mapping before `main`. The new native harness
checks these production-loader transitions:

1. Process startup and provider path configuration leave the marker absent.
2. Actual `rt_vulkan_device_count` demand returns the fixture's value and writes
   exactly one constructor marker, `C`.
3. 128 repeated capability requests return expected fixture results while the
   marker remains `C`.
4. Explicit unload produces `CD`, proving repeated demands did not leak loader
   references. A new demand and unload produce `CDC` then `CDCD`.

A separate mutation control preloads the real fixture using `LD_PRELOAD`.
Its constructor runs before `main`, and the same observer must reject it at
the first assertion with exit 10. No actively loading getter is used to
observe the pre-demand state. Existing admission and dispatch cases remain.

Validation ran once on WSL Ubuntu against release `32491995db3` plus this
script change, using the existing native C loader test recipe. The process-tree
watchdog enforced 5859375 KiB and a 300-second timeout; it completed with exit
0 and peak RSS 108632 KiB. The log reported all four new demand/lifetime
assertions true and all prior registry checks passed. Shell syntax passed.
Retained evidence is `D:/dev/simple/build/review/item5-gpu-demand.log` and
`item5-gpu-demand.rss.env`.

This fixture deliberately returns controlled device/operation values to test
the real loader boundary. It is not a real Vulkan/CUDA kernel, authenticated
generic provider ABI qualification, a no-import Simple executable measurement,
or evidence for every optional-provider family or host. It does not establish
AVX512 execution, application correctness/performance, or full item 5 completion.

## Real CUDA bitmap component supplement, 2026-11-07

This supplements the historical controlled loader fixture; it does not replace
that evidence or close its separate Simple-application acceptance gaps. Frozen
source `41d9151614adbaadb098b871894537e90593a70f` was materialized privately and
the unchanged `scripts/check/check-cuda-bitmap-provider-v1.shs` executed on WSL
Ubuntu with a Quadro P4000, UUID
`GPU-c44a4537-6124-77b1-e956-28f2cb13d734`, driver 582.78, 8192 MiB.
The provider embeds PTX 6.0 targeting sm_61; no nvcc/NVRTC or toolkit installation
was needed. No production source or system toolchain was changed.

The default invocation and the existing `--maximum-only` invocation both exited
0. The latter reused the exact compiled provider/runtime objects and executable.
The canonical loops executed these nine device operations; raw output reports
aggregate invocation results, not separate per-size timing measurements:

| Invocation | Words | Result |
|---|---:|---|
| default | 1 | exact device readback |
| default | 31 | exact device readback |
| default | 32 | exact device readback |
| default | 33 | exact device readback |
| default | 127 | exact device readback |
| default | 128 | exact device readback |
| default | 129 | exact device readback |
| default | 1025 | exact device readback |
| maximum-only | 16384 | exact device readback |

The independent bitwise oracle checked every output word and receipt checksum.
Default output records authenticated=true, launches=8, words=1506, canaries=128,
copied_input=true; maximum-only records launches=1, words=16384, canaries=16.
Both verify caller/thread CUDA-context preservation and resource/completion
ownership. The bad-digest invocation passed with driver_unloaded=true. Loading
the valid provider descriptor also left libcuda unloaded until device demand.
The adjacent exhaustion/timeout/drain/destroy/context failure-policy selfcheck
passed with **mocked_driver=true**; it is not actual GPU fault injection.

Both device watchdog receipts record status=complete, exit_status=0,
quiescent=1 and no unexpected session PIDs, under 60-second/1000000-KiB caps.
Device-process peak RSS was 156648 KiB and 125740 KiB respectively. The bounded
compile coordinator observed 185392 KiB owned-group peak, with a 1-GiB cap and
4-GiB shared memory/disk reserves. These values and retained kernel event times
are diagnostic observations, not a hardware performance comparison.

Exact artifact/runtime authority:

| Artifact | SHA256 |
|---|---|
| provider.so | `38e57f79a2c343b2c1ffc1a1b8c5d5574925b58f381a660af3a5f73a37516b7d` |
| check | `df57efd17fdb0763efb5e7850f2b3ec85ff4eadf14da19a840c7b4dde00eccea` |
| runtime_native.o | `1de039c6e0a0d45487201ffd9f5292fff3b636a33e88ce67747039e276bc7d5d` |
| runtime_dynload.o | `6515cebb8ecb781af3949dc6e262ce2f38f84ad7999102d337cd1d28dd9e63a5` |
| /usr/bin/x86_64-linux-gnu-gcc-15 (15.2.0) | `b5f1b773a7c733738352000c92a077dc5852a1a2fc6d836b1e411be1e9ec5f88` |
| /usr/libexec/gcc/x86_64-linux-gnu/15/cc1 | `30510b346885152c4fce41d2b501751c95d3690b1c34eaa04ebb970e70eae620` |
| /usr/bin/x86_64-linux-gnu-as | `4e5fcaa3cdc160173cb5cfe7aa35dc39d7aa1f06ba8d75b8d923bbae5473991b` |
| /usr/bin/x86_64-linux-gnu-ld.bfd | `97f48d93b8b076a92d2809ec29dcb17f0f37c8827358f832255e2ed22fef6075` |
| /usr/lib/wsl/lib/libcuda.so.1 | `230d2b53d4489cc8600adc9a31bf074a46e2705bf11f11f5741723ba81e18378` |
| /usr/lib/x86_64-linux-gnu/libc.so.6 | `85e64f97e348786a8fb4d9f3d52fec289e2fb86bba20f0731dfe61990525e0f7` |

No Simple runtime archive was used: the two frozen-source C runtime objects
above are the runtime authority. ELF dependencies are libc for the provider
and libc/libm for the executable, with no direct CUDA link dependency.

Durable evidence root:
`D:/dev/simple/build/review/item5-cuda-component-41d915-20261107/`.
`retained-canonical/` contains compiled artifacts, compile/source manifests,
failure/denied/device logs and the default watchdog receipt;
`maximum.stdout` and `maximum.rss.env` retain the maximum case. POSIX originals
remain under `/root/item5-cuda-component-41d915-20261107/`.

| Ledger | SHA256 |
|---|---|
| source-identity.json (443 exact owned files) | `418c91c9a2c42963311720a4673dcf6237b39dadcdc2f22dc7fc9cb14acbe037` |
| tool-device-runtime-identities.json | `39b1e3c7e962d2669a4a31af0152484b639cad7b85c8274e5c055d2b31cdebc0` |
| summary.json | `fb56512a3769acc5a6f66e2eeff8f5e2ae7344103461813645228753b2ab2f6d` |
| validated-receipts.json | `c43d73a9a9538826efed15a8fd6d5cfd5609db318b995ddf80161fd12c7f8210` |

**Remaining scope:** bad-digest refusal and demand-load assertions are not a
driver-unavailable host test or a CUDA-off Simple build. The legacy
`check-cuda-dlopen-fallback.shs` requires a matching `libsimple_runtime.so`
and its separate `rt_cuda_*`/`SIMPLE_CUDA_LIB` contract; no matching frozen-source
shared runtime was available here, and another generation was not substituted.
Real Simple DB/HTTP provider sessions, compiler CUDA backend placement, full
bootstrap, CUDA-versus-CPU performance and full item 5 acceptance remain open.
The canonical receipt explicitly reports device image authority=none. No
successful test or compilation was repeated for this documentation append.
