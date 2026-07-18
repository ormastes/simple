# TLDR: Async / Green-Process Hardening Plan

Goal: finish green-process lane (share-nothing: no shared variables across
green tasks/processes), fix async runtime/compiler holes, harden process IPC,
add missing async primitives. Security issues fixed inline (`sec(...)`).

```sdn
flow:
  audit[5-lane audit] -> w1[Wave 1: lib fixes (parallel)]
  w1 -> w2[Wave 2: enforcement + hard fixes]
  w2 -> w3[Wave 3: verify interpreter-mode + commit]
  w1: async runtime repair | process_set IPC sec | env fixes | semantics doc
  w2: E-PAR share-nothing rule | green_thread deglobal | await crash guard
```

Initial state found: std.async runtime broken (write-only wakers, no-op
sleep/yield, hollow specs); `async fn`+`await` SIGSEGV in interpreter;
greenprocess ~90% done with no share-nothing enforcement; process_set file-IPC
racy (security). Current handoff state: E-PAR-006 share-nothing enforcement is
live in the self-hosted `simple check` path, including lambda call arguments.

Wave 1 (easy/parallel): repair async/runtime.spl + wakers + combinators;
atomic IPC + reaping + kill guards; refresh stale check binary + submodule;
semantics decision doc for 20 uncovered checklist items.

Wave 2 (hard): mutable-capture misuse rule for spawn surfaces (core ask),
de-globalize green_thread, await-crash guard, actor dispatch, async
timer/timeout/cancellation/channel/mutex primitives.

Full plan: async_green_process_hardening.md
