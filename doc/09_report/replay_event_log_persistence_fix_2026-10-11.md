# Replay event-log persistence repair — 2026-10-11

Status: **three reproduced host persistence failures repaired and verified by a non-admitting historical-seed diagnostic**. The final manual is `doc/06_spec/03_system/tools/replay_event_log_spec.md`; its complete executable source mirrors the canonical spec.

The original empty writer retained stale bytes and incorrectly accepted an `events.bin` directory; the reader accepted a missing event file as an empty trace. The repair uses the existing SOSIX host facade, three thin canonical I/O aliases, unconditional binary replacement including empty arrays, and strict text/binary read errors. It removes the shell/hex workaround without adding a mock filesystem, runtime extern, FAT32 dependency or OS boot dependency.

| Diagnostic | Executed | Passed | Failed | Duration | Exit | Peak tree RSS |
|---|---:|---:|---:|---:|---:|---:|
| Cycle one, unchanged owner | 30 | 27 | 3 | 1001 ms | 1 | 230168 KiB |
| Cycle two, repaired owner; original cases 28–30 only | 3 | 3 | 0 | 223 ms | 0 | 254868 KiB |

Both runs reported zero skipped/dropped cases and quiescence 1. All 67 cycle-one and 71 cycle-two input hashes matched before/after execution. The 27 green cases were not rerun; there was no third cycle or complete final-source 30-case rerun. The failing rewrite case gained a nonempty read-back comparison of all twelve fields of both records, directly checking the changed byte conversion. Fixtures use uniquely owned temporary directories with checked cleanup.

Evidence root: `build/phase-one-storage-gui-diagnostic/`. Baseline receipts: `replay_event_log_spec/cycle-one.{log,rss.env,exit}`. Final receipts: `replay-event-log-persistence-cycle-two_spec/cycle-two.{log,rss.env,exit}`. Input manifests: `event-log-cycle-one-inputs.sdn` and `event-log-cycle-two-inputs.sdn`. Selection mapping: `replay-event-log-persistence-cycle-two-mapping.sdn`. Separate status: `replay_event_log_spec/final-status.sdn`.

Historical producer SHA-256: `0cceac635e63781b7bf9bc9830735e948986de223434eca46d84eb35233f8b17`. Current mutable marker/preflight are absent and were not recreated. Generation integrity identifies the producer, not current admission.

Final owner SHA-256: `b55165465bac8ed889e358122da337ca757187eaeee05c29b384fc012b5af5a6`.
Final facade SHA-256: `31ce0a227262901e6de7e3bf4d6f26ec2ad5b3e34f39530f71cd6c4d9ae63625`.
Final canonical spec SHA-256: `16c00bebe8d825970cb5a90884e92d9ab267e8141d882f7e977ca30a0623ddf1`.
Final derivative SHA-256: `4fe2e0d636bf54c9b42bf9b4dc7286aeae123c6a821b3e727215651e00dd7b7e`.

No current Phase1/full CLI, native, Windows, VM, full replay or measured coverage qualification is claimed. Partial records, signed-negative codec values, full manifest restoration, two-file transactional publication and durable close-error reporting remain outside this repair.
