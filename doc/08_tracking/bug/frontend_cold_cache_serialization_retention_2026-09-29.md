# Cold frontend cache serialization retains temporary allocations

Frozen source `5da86869df060ad4c1b87abfd2384f8d2a761e3a` produced the admitted Linux Stage2 compiler SHA256 `a45ede92cdbb972d26369ccaa6c42960ec2fca64e560e106ec7a0ca2c8e3747b`. Its mandatory full matrix failed during CLI parsing at 384/2444 files and runner parsing at 427/603 files under the unchanged 5,859,375 KiB RSS cap. MCP/LSP HIR segmentation faults are a separate receiver ownership defect under independent investigation.

## Measured isolated baseline

A supported parse-only static shard `0/4` of the runner closure parsed exactly 155 files / 2,411,774 source bytes with that same admitted compiler, then exited before HIR. Each variant had separate D ext4 HOME/tmp/cache/output, a 180-second bound and the original RSS guard.

| Variant | Wall seconds | Peak RSS KiB | Parsed files | Stored cache bytes |
| --- | ---: | ---: | ---: | ---: |
| Cold cache on | 28.25 | 2,153,832 | 155 | 11,347,375 |
| Cache off diagnostic control | 21.22 | 1,476,948 | 155 | 0 |

Cache serialization adds 676,884 KiB (45.8%) and 7.03 seconds (33.1%) in this probe. This does not explain all retained parser/AST memory. Disabling the cache is a diagnostic control, not the production fix.

Evidence: `D:/dev/simple-wsl-recovery-20260928/linux-5da-terminal-incident-20260929/incident.json` and `/mnt/simple-bootstrap-6b2/linux-5da-parse-cache-diagnostic-cycle1-20260929/comparison.json`, with exact invocation/env, RSS receipts and logs per variant. The CLI summary reports 114 seconds and peak 5,862,680 KiB; the runner reports 95 seconds and peak 5,860,948 KiB.

## Narrow lifetime repair

Ordinary cold cache stores now serialize inside a short transient heap scope. The existing runtime owner promotes the final text blob before scope end, which reclaims encoder arrays, per-element strings and intermediate joined blobs. The returned ParserModule and source pools predate this scope and remain retained. The two nested declaration pool reconstructions now use local encoder views rather than installing temporary children in global pool owners. Serialization bytes, ordering, format version, cache identity, cache-on behavior, parser diagnostics and public language semantics are unchanged.

The existing streaming parser path already has a paused scope; it retains its established behavior and does not open a nested scope. Required scope/promotion failures fail closed.

The focused executable spec covers exact blob equivalence, function data retained across a second parse and a cache restore. It is written but not executed yet. The edited compiler must be compiled into a new producer before the same 155-file diagnostic can measure this repair; running the old admitted producer against edited source cannot demonstrate lower parser RSS. No improved memory/time or full bootstrap PASS is claimed yet.

The minimal admitted bootstrap compiler does not supply the complete optimizer application as a ready compiled artifact. Generic optimization was not delegated to the Rust seed. Source ownership and measured lifetime evidence guide this change; optimizer CLI execution and broader core/MCP checks remain pending a capable rebuilt producer.
