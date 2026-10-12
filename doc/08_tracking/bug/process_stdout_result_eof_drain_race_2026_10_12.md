# P1: stdout drain state is conflated with process liveness

Status: SOURCE-CONFIRMED, native facade reproducer UNEXECUTED. Exact frozen82 source src/lib/nogc_sync_mut/io/process_ops.spl:863–869 reads a chunk, returns nil if the process is alive, otherwise reports process_stdout_eof. Canonical Windows rt_process_is_alive frees the entire shared slot when the child exits, including stdout handle and decoder state. Astra independently classified this as a P1 end-to-end gap.

Concrete sequence: the process writes a valid incomplete UTF8 prefix at the last poll (for example E2 82); primitive read retains it until EOF and returns owned empty text. Child exits before the facade liveness check. is_alive frees the pending prefix; the facade returns EOF without allowing the read to flush U+FFFD according to established Rust lossy policy. A similar race can drop ordinary output that becomes readable between the empty read and the liveness check.

Primitive framing tests against Rust std String::from_utf8_lossy passed14209 checks, including pending prefix→EOF replacement. Those tests do not execute the facade. The authored native primitive fixture drains stdout before calling is_alive and therefore does not prove this gap repaired.

Required proper fix: represent stdout EOF/drain state independently of process liveness; retain exited-child output/state until drain completion or explicit close; coordinate the pure-Simple Result facade and runtime owner cleanup. Do not make a dead child appear alive to avoid the error. Preserve bounded registry cleanup and job ownership. This coordinated consumer fix is outside the present source-only six-primitive projection and is not merged, built or qualified.
