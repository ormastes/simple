# Phase 1 native smux compares unsigned revision counters as signed

The Linux x86-64 Phase 1 seed built smux from `release/1.0.0`, and the resulting owner accepted an authenticated `list` request with zero sessions. Its first `new` request returned `smux: session capacity reached`.

The executable's `os__apps__smux__service_revision__service_revision_new` initializes `value` to `1`. Disassembly of `os__apps__smux__service_revision__service_revision_writable` shows `cmpq $0xfffffffffffffffe,(%rbx)` followed by `setl`, the signed less-than instruction. That rejects `1` because the revision limit is interpreted as `-2`. The unsigned comparison should admit `1`.

The failing producer was built from `a685c58a3f0a86e82f28853431142dde8782946a`. Its SHA-256 was `73b271d1a703b7279ded7559aba08610f4459e8c5a132e04675752289c685300`.

The revision workaround let the first `new` request create a session. PTY attachment still failed because `PaneRecord.can_attach` lowered its maximum-counter comparisons with the same signed instruction. `PaneRecord.can_ingest` also emitted signed ordering against its byte-ingestion limit.

The smux owner uses equivalent equality checks at the zero and maximum `u64` sentinels. It still reserves the final revision for cleanup. Its ingestion guard uses a mask for the same final 1 MiB of the `u64` range. The Rust seed's native unsigned field comparison needs its own compiler regression. The smux owner spec covers the final writable revision and reserved cleanup tick in `test/03_system/tools/smux_coremux_owner_spec.spl`.
