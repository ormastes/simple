# Slang bounded serial multi-prefix cache architecture

Date: 2026-09-08. Status: S2 implementation architecture.

Simple owns request sequencing and configured count/byte limits. The ggml shim
owns a fixed-capacity table of opaque immutable llama sequence snapshots and
their exact tokenizer IDs. The fixed table bounds metadata; dynamic state and
token allocations are included in one retained-byte gauge.

Before prefill, the shim scans at most eight entries and chooses the longest
complete token prefix. A successful restore removes and recomputes the trailing
boundary token. Restore/truncation failure invalidates that entry and clears the
live context. After successful prefill, an exact duplicate only refreshes LRU;
otherwise the owner evicts least-recently-used entries before allocating and
serializing a candidate. Candidates larger than the byte ceiling are rejected.

The compatibility ABI keeps S1 symbols mandatory and resolves S2 configuration
and gauges optionally. Capability bit 8 means bounded serial multi-entry
retention. It does not mean A4 paged KV. The single global execution context
still serializes requests; independent contexts and copy-on-write pages are the
next ownership boundary.
