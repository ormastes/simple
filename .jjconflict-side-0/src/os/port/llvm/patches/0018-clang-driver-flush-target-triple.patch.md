# Clang driver target-triple stdout flush patch

Small `llvm::outs()` writes can remain buffered in the freestanding SimpleOS
Clang artifact when the command exits before the stream buffer fills. This makes
canonical host smoke commands such as `clang --print-target-triple` return exit
code 0 with empty stdout, even though larger stdout paths such as `--help`
write correctly.

Patch `clang/lib/Driver/Driver.cpp` to explicitly flush `llvm::outs()` after the
early `--print-target-triple` and `--print-effective-triple` handlers:

```cpp
if (C.getArgs().hasArg(options::OPT_print_target_triple)) {
  llvm::outs() << TC.getTripleString() << "\n";
  llvm::outs().flush();
  return false;
}

if (C.getArgs().hasArg(options::OPT_print_effective_triple)) {
  const llvm::Triple Triple(TC.ComputeEffectiveClangTriple(C.getArgs()));
  llvm::outs() << Triple.getTriple() << "\n";
  llvm::outs().flush();
  return false;
}
```

This keeps the behavior equivalent on hosted platforms and makes the SimpleOS
cross-Clang host-smoke output deterministic without adding another libc stdout
buffering layer.
