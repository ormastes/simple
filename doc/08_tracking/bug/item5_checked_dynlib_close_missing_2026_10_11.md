# Provider loader called a missing checked close facade

The de400/Phase2-75c DB-vector and HTTP-vector native builds reject
`provider_loader.spl`: `os.posix.dynlib` exports no `dynlib_close_checked`.
Both admission cleanup and owned-session close already expect an `Ok/Err`
result and retain their original open generation on failure.

Implement that public facade in the existing dynamic-loader owner by calling
`dynlib_close` once. Return `Ok(0)` only for zero; preserve every nonzero
platform/kernel status in `Err(status)`. Keep the provider loader's cleanup
and retry ownership branches unchanged.

Both C `runtime_native.c::rt_host_dynlib_close` and the Rust runtime equivalent
return POSIX `dlclose`'s actual status. Their Windows path maps successful
`FreeLibrary` to zero and failure to minus one. The SimpleOS async registry
normalizes successful release to zero and preserves negative errno failures.
Thus a sign test or unconditional success would erase a real host close error;
zero equality is the shared contract. PE-format opening remains unsupported in
this facade, and no platform support expansion is claimed.

`test/fixtures/os/smf/dynlib_close_checked_main.spl` checks invalid variant,
invalid host handle, real registry EBADF, and successful close of one real
host-loaded library supplied by path. It never passes an invented positive
pointer to dlclose or attempts unsafe duplicate close. The registry case checks
preservation of a real backend error; Windows execution needs a Windows host
library and remains unexecuted here. A true OS dlclose/FreeLibrary failure after
a valid open is not injected by this fixture and is not claimed as exercised.

Status: source and native regression authored; execution and provider-loader
integration remain pending the root-owned repaired compiler. No release PASS.
