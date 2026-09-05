# LLVM Support SimpleOS Path Patch

SimpleOS cross builds use LLVM's generic Unix `Path.inc`, but upstream LLVM has
no `GetMainExecutable` branch for the `unknown-simpleos` OS component yet.

Patch `/home/ormastes/llvm-project/llvm/lib/Support/Unix/Path.inc`:

```diff
+#elif defined(__simpleos__)
+  if (argv0 && argv0[0])
+    return std::string(argv0);
 #else
 #error GetMainExecutable is not implemented on this host yet.
 #endif
```

This is a compile-enabling fallback. It deliberately returns `argv0` until
SimpleOS grows a kernel-backed `/proc/self/exe`, auxiliary vector, or dynamic
loader path query.
