# LLD Filesystem No Async Unlink Without Threads Patch

## Problem

SimpleOS cross tools are built with `LLVM_ENABLE_THREADS=OFF`. LLD still used
`std::thread` in `lld::unlinkAsync` when overwriting an existing output file,
which made host-run smoke tests fail with `thread constructor failed`.

## Patch

In `lld/Common/Filesystem.cpp`, make `unlinkAsync` remove the existing path
synchronously when `LLVM_ENABLE_THREADS` is disabled:

```cpp
#if !LLVM_ENABLE_THREADS
  sys::fs::remove(path);
  return;
#endif
```

This keeps the existing async performance path for threaded hosts and avoids
requiring a real pthread implementation for the SimpleOS no-thread cross build.
