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
