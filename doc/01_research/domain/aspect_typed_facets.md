<!-- codex-research -->
# Typed facet domain research

Dynamic dispatch tables contain code pointers and must not outlive their module.
Use an explicit versioned descriptor and host-owned identity rather than a
native trait-object or dynamic-loader handle as a public ABI.  POSIX and Windows
both invalidate symbols after unload; native handles may be reused.

The safe lifecycle is: revoke publication, reject new leases, await active
leases, run shutdown, then close.  Generation identity prevents slot/handle
ABA.  A `FacetRef<T>` should carry host-owned `(facet_id, module_id,
generation)`; a scoped lease alone holds descriptor/context/function pointers.
The current repository has only payload-only V1 unpin and a proposed
receipt-owner bridge, so this lifecycle is a requirement option rather than an
available executable-unload implementation.

Sources: [Rust trait objects](https://doc.rust-lang.org/reference/types/trait-object.html),
[POSIX dlclose](https://pubs.opengroup.org/onlinepubs/9699919799.orig/functions/dlclose.html),
[Windows FreeLibrary](https://learn.microsoft.com/en-us/windows/win32/api/libloaderapi/nf-libloaderapi-freelibrary),
and [libloading lifetime guidance](https://docs.rs/libloading/latest/libloading/).
