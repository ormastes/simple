# Rust UTF-8 AVX2 is prefix-only and width index costs 8 bytes/scalar

The Rust `utf8_kernels.rs` AVX2 path scans only an ASCII prefix, then calls the
scalar standard-library validator/count/finder. On a 656 KiB mixed-valid corpus,
Criterion reports only near-parity with scalar (1.23 versus 1.21 GiB/s), so the
old SIMD-complete status is not supported by executable evidence.

The width/rank-select implementation stores every scalar start as `usize` in a
global mutex registry. Measured storage is exactly 8.00 bytes/scalar before
HashMap, allocator, and locking overhead.

Replace validation with a complete vector algorithm plus scalar oracle parity.
Replace default random-access storage with owner-bound sparse checkpoints;
benchmark a succinct continuation bitmap separately. Required evidence includes
bytes/source byte and scalar, build/query/free latency, allocations, RSS,
post-free retention, and contention scaling.
