# Darwin: worker code-address probe also matches DATA (dladdr fallback)

Status: OPEN. Found 2026-11-07 in review of PR #7420 / #7432.

`src/runtime/runtime_thread.c` `rt_native_address_is_code` has a real
executable-range test on Windows (`VirtualQuery`) and ELF hosts
(`dl_iterate_phdr`), but on macOS it falls back to
`dladdr(...) != 0 && dli_fname != NULL`, which is also true for DATA addresses
inside the image (its own comment says so).

`spl_worker_callable` uses the probe twice: the #7420 bare-entry fast path
(a non-capturing fn value passed as its bare entry address) and the decoded
payload check right after it. On macOS a TAG_HEAP word pointing at a static
closure record in `__DATA` can therefore be taken as code and called.
Guarding only the fast path (tried in #7432, reverted) brings back the #7420
crash for bare entries and leaves the second site exposed.

Fix: a Darwin probe twin of `VirtualQuery` — `mach_vm_region(mach_task_self(),
&addr, &size, VM_REGION_BASIC_INFO_64, ...)`, require the returned region to
contain the address and `info.protection & VM_PROT_EXECUTE`. Needs a macOS
host to compile and test (none on the Windows host where this was found).
