# BUG: [CODEGEN-STUB-FALLBACK] silently replaces functions with empty stubs and exits 0

**Date:** 2026-06-11
**Status:** OPEN
**Severity:** High (silent miscompile)
**Found by:** memory_audit_gc_nogc nogc verification (.spipe/memory_audit_gc_nogc/research_nogc_verify.md §7 B3)

## Problem

`bin/simple compile <file> --native` on a file importing `std.gc_async_mut.gpu` prints

```
[CODEGEN-STUB-FALLBACK] ... 'gpu_global_size_z': rt_gpu_num_groups not found
```

replaces the function body with an empty stub, and **still exits 0**. The produced
binary silently does nothing where the stubbed function is called.

## Why this is bad

- A missing runtime symbol is a hard link-level error being downgraded to a warning
  string + wrong code. This is the same false-green family as compile-mode no-op
  stubs (see feedback_compile_mode_false_greens memory note).
- Combined with the gc-boundary lint not running at compile time, a nogc target can
  import gc-tree GPU code and get a silently-stubbed binary with exit 0.

## Expected

Unresolved rt_* symbols at codegen must fail the compile (non-zero exit) unless an
explicit `--allow-stub-fallback` opt-in is given.
