# Caret JIT run splices 392 externs through the interpreter (unregistered JIT symbols)

- **Filed:** 2026-11-13
- **Status:** OPEN. Out of scope for lane `work/jit-dynamic-dispatch-20261113`; tracked here only.
- **Related:** `doc/05_design/compiler/jit/jit_trait_dispatch_and_cross_module_link.md` (row 5)

## Symptom

`SIMPLE_RUST_SEED_WARNING=0 <seed> run src/app/llm_caret/main.spl --help`
(seed `a64ac53aaf6ca014`, `origin/release/1.0.0` `fe75b13a584`) prints:

```
[engine-demotion] reason=hybrid-interp-splice detail=rt_stdin_read,rt_local_unix_close_v1,...
```

The list has 392 names. This is a **partial** demotion, not a module drop.
`run_file_jit` (`src/compiler_rust/driver/src/exec_core.rs`, the
`unresolvable_externs` block) finds every extern declaration whose name has no
symbol in the JIT symbol provider. It rewrites each call to that extern into an
`InterpCall` bridge, which the interpreter's extern table resolves by name at
run time. The rest of the module stays JIT-compiled. The cost is one
interpreter round-trip per call to these externs, plus the receipt naming the
splice.

## Breakdown (origin run)

| Class | Count | Examples |
|---|---|---|
| Win32 / Windows API names | 32 | `CreateProcessW`, `GetTickCount64`, `BCryptCreateHash`, `HeapAlloc` |
| other non-`rt_` names (`pmm_*`, `retained_native_*`, ...) | 11 | `pmm_alloc_page`, `retained_native_close` |
| foreign-platform `rt_*` (kqueue, iocp, event ports, arm, port I/O) | ~32 | `rt_kqueue_register`, `rt_iocp_poll`, `rt_event_ports_create`, `rt_port_outb` |
| host-applicable `rt_*` not registered in the JIT provider | ~317 | `rt_process_*` (76), `rt_simd_*` (57), `rt_linux_*` (25), `rt_http_*` (23), `rt_local_*` (18), `rt_file_*` (11, e.g. `rt_file_atomic_write`, `rt_file_modified`) |

## Fix directions (owner decision)

1. Register the host-applicable `rt_*` in the JIT symbol provider, either by
   adding them to the runtime symbol table or by checking that they are
   exported and `dlsym`-visible.
2. Cfg-prune the platform-foreign extern declarations from the host unit, so
   they are never declared and never spliced.

Neither is a by-name method dispatch or a cross-module link problem.

## Reproduce

```
SIMPLE_RUST_SEED_WARNING=0 <seed> run src/app/llm_caret/main.spl --help 2>&1 \
  | grep 'reason=hybrid-interp-splice' | sed 's/.*detail=//' | tr ',' '\n' | sort
```
