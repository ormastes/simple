# Bootstrap atomic update deprecation (2026-11-09)

Phase Ladder run 42551927129 emits 108 repeated owned-code diagnostics for six
`fetch_update` call sites: SHA-256 counters in compiler/runtime, Vulkan handles,
two recursion-depth decrements, and transient-array scope identities.

The bootstrap pin is `nightly-2026-09-15` (installed rustc 1.100.0-nightly,
574ff7d98). Owned workspace manifests declare no `rust-version`. Installed
stable 1.93.1 documentation still marks `try_update` as nightly-only
(`atomic_try_update`, issue 135894). A direct rename would therefore add a
compatibility requirement. The shared `simple_common::atomic_update` helper
uses the established load/compare-exchange-weak loop instead, without feature
gates, lint suppressions, or manifest/toolchain changes.

The failure ordering governs the initial load and failed exchange; the success
ordering governs a successful exchange. A failed exchange passes its newly
observed value back through the mutable callback. A declined callback returns
that observation without writing. Each caller retains its original orderings,
checked arithmetic, return mapping, exhaustion sentinel, and reset behavior.

## Focused verification

`python scripts/check/check-rust-atomic-updates.py --output <external-dir>`
compiles the actual helper plus all six call expressions extracted from their
owners, with `-Dwarnings`. It runs four tests: actual owner calls, checked
boundaries (including transient u32 wrap-to-zero), callback retry then refusal,
and eight-thread allocation contention with exactly 512 unique handles before
exhaustion. Stable 1.93.1 and pinned nightly both PASS (4/4 each).

Retained artifacts: `D:/dev/wt/msvc-warning-evidence-20261109/atomic-stable-pass`
and `atomic-pinned-pass`. These are bootstrap Rust codeunit regressions, not
self-hosted product or Phase Ladder admission evidence. Full parent lane
verification and fresh CI remain separate.
