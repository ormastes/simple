---
name: feedback-pure-simple-first
description: Implement features in pure Simple before wiring C/Rust backends; optimize with optimize plugin after
metadata:
  type: feedback
---

Implement in pure Simple first, not C or Rust backed. Optimize with optimize plugin after getting it working.

**Why:** User wants Simple-native solutions; C/Rust FFI backends are a later optimization step, not the first approach.

**How to apply:** When building new runtime features (I/O drivers, servers, etc.), start with a working pure Simple implementation using existing extern primitives. Only wire C/Rust backends after the Simple version works and benchmarks show where optimization is needed. Related: [[feedback_fix_spl_not_rust]]
