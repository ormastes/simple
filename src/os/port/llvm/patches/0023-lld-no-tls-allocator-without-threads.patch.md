# LLD: avoid TLS allocators when threads are disabled

SimpleOS builds LLVM with `LLVM_ENABLE_THREADS=OFF` and does not yet provide an
ELF TLS runtime. In `lld/include/lld/Common/Memory.h`, include
`llvm/Config/llvm-config.h` and make `getSpecificAllocSingletonThreadLocal()` use
`static SpecificAlloc<T>` when `LLVM_ENABLE_THREADS` is false; retain
`thread_local` for threaded builds.

This removes the otherwise unresolved `__tls_get_addr` from the embedded-LLD
Clang executable without adding a fake TLS resolver.
