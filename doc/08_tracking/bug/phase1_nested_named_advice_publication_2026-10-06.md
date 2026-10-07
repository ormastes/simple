# Phase1 nested named advice dispatch and publication

Nested named functions resolve through lexical Function values before flat-table dispatch. That path omitted before/after advice interception. Adding interception exposed a second defect: direct advice-body execution did not publish global writes through ordinary call-exit synchronization, so the next named call restored stale values.

The named Function branch now runs matching before and after advice around its existing captured-environment execution. Advice execution synchronizes owned captured globals before copying existing caller bindings back. Anonymous lambda dispatch retains its existing behavior.

Three regression examples passed under the enforcing 5859375 KiB watchdog: wildcard before calls, after-success/error selection, and lexical alias dispatch. Original failure was 0/3; adding publication produced 3/3. Two lambda-return controls, two advice-dispatch error probes, and two ordinary global-write controls narrowed the failure before the final patch. No passing controls were rerun. Raw evidence: /tmp/simple-aop-diagnostic/advice-sync.log and advice-sync.rss.env.

This is a bootstrap Rust seed repair. The whole seed sweep is still running against its original immutable compiler/source; its AOP product spec requires a later repaired seed. Phase2–4 and release admission remain incomplete.
