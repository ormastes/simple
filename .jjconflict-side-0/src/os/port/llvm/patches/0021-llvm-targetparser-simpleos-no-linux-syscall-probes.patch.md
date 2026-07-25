# LLVM TargetParser SimpleOS no-Linux-syscall probe patch

LLVM `Host.cpp` treats Linux+x86_64 as permission to call raw Linux
`syscall(...)` for the BPF CPU-version probe. SimpleOS cross builds can inherit
Linux-style CMake feature paths while compiling with `__simpleos__`, and the
SimpleOS libc intentionally does not expose a generic Linux `syscall` ABI.

Patch `llvm/lib/TargetParser/Host.cpp` so SimpleOS takes the generic BPF CPU
name path:

```cpp
#if !defined(__linux__) || !defined(__x86_64__) || defined(__simpleos__)
  return "generic";
#else
```

This keeps the Linux BPF probe on real Linux hosts and avoids adding a
speculative libc `syscall` compatibility surface for SimpleOS.
