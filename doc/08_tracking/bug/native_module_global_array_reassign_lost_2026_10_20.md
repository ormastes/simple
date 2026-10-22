# Native: reassigning/pushing a module-level `var` array from `main` is lost

- Canonical id: native_module_global_array_reassign_lost_2026_10_20
- Date: 2026-10-20
- Status: open (found while verifying PR #3914; not caused by it)
- Producers: producer6 strict (release_phase3 1622d7c0c7a) AND a producer rebuilt from
  work/p6-mir-misc — identical output, so pre-existing.
- Repro (native-build, llvm, x86_64-pc-windows-msvc, core-c-bootstrap):

  ```
  var IDS: [i64] = []
  fn main():
      IDS = IDS + [3]
      IDS.push(4)
      print "global_len={IDS.len()}"
  ```
  prints `global_len=0` (expected 2). A module-level `var EVENTS: i64` incremented from a
  function works, so the loss is specific to array-valued globals (reassignment and push).
- Impact: a registry kept in module-level arrays silently stays empty, e.g. the pattern in
  `src/lib/nogc_async_mut/thread_pool.spl` (`GLOBAL_TASK_VALUE_IDS = GLOBAL_TASK_VALUE_IDS + [task_id]`).
- Owner: MIR/backend global storage; not investigated further.
