# Phase 2 runner recovery evidence — 2026-10-30

The user replaced the six-cycle stop with a 12-hour work window ending 2026-10-30 08:47:02 UTC. Historical evidence and failures are preserved; no full product qualification is claimed.

## Attempt 7

Source HEAD 36d94ddbc095308ab18b6bed30555350bee7f18b plus three owned runner deltas; admitted source inventory 77b0c97831ffd7f1f7c04e1b85b9088369e30c2714697e3f2d4bc55c3444864a. Compiler a9ed5e4b92a811fa14f5ae351948c8d4350527f966139ea72ac13ccee3633e4f. Native build compiled 1616 modules with zero failures; sanity and receiver admission passed. The Rust seed emits one-binary, not requested dynload.

The actual Hello executable printed exactly `hello`, exit 0. The canonical nonreceipt check reported two cases PASS. This is diagnostic evidence, not an official Item5 receipt: the helper was x86_64-only and the producer originated from a dirty source checkout. A reconstructed clean snapshot is not substituted for its actual origin.

CLI failed at unresolved `file_is_symlink` in inventory_scan_v2.spl. Aggregate watchdog peak was 43,187,920 KiB under 50,331,648 KiB; exit 1, quiescent. The summary value 15,600,152 KiB is per-process rusage and must not be reported as the tree peak. This is partial-workload resource evidence, not full CLI or comparative performance qualification. Runner lowered 288/304 modules, 16 BLOCKED (previously 285/304 and 19 BLOCKED). Seven selected native module diagnostics passed; broader inventory and product tests remain incomplete.

Memory policy landed through PR5315. Real no-follow stats traversal landed through PR5316 after a native filesystem regression with verified real symlinks and exact counts/SLOC.

Actual MIR carrier and qualified-route probes did not execute: serial attempts timed out with progress; parallel continuations retained incomplete dependency inventories, with no crashed worker. The additional failed-worker count represents incomplete inventory, not evidence of a scheduler accounting bug. Compatible partial caches and failed receipts were retained.

## Attempt 8 preparation

Isolated worktree: /tmp/simple-phase2-runner-attempt8-20261030. Branch: work/phase2-runner-attempt8-20261030. Release base: 33189d6fc7d6150b2003f2bfcd5eaaca107b3963. Owner /root integrates reviewed changes only.

Pending runtime qualification: MIR declaration-root scope; qualified-export dependency discovery; bounded missing-provider diagnostics; shared authoritative worker resolution; AArch64 prospective Hello receipt; runner lane behavior. These are local candidates, not merged or product-qualified unless separately stated. The next producer must originate from a clean local snapshot commit. Preserve that checkout unchanged; runtime receipts and subsequent evidence belong outside the frozen source.

Acceptance remains the full requested CLI/runner behavior: comment doctests, Markdown, SSpec, plain/bare test routing and failure counts, enabled logging, required core/MCP checks, and reviewed merged runner changes.
