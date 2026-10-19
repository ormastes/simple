# Canonical CAS publication and FIFO refusal qualification

Status: **ACCEPT_STATIC; C-provider ABI qualification PASS (21 cases).**
Simple CAS11, Rust-provider execution and full runtime qualification remain
**HOLD/UNRUN**.

The canonical CAS publication fix is frozen at `fe1bb38b5d2` on base
`f2021f4e833acfc0334ca9f93e17a8f60950283b`. Its four source/spec/documentation
files remain unchanged alongside the separately reviewed provider correction.

## Contracts and ownership

`cas_put(root: text, content: text) -> text` returns the candidate SHA-256 digest
only after reading identical bytes through the bounded regular-file no-follow
facade. Deduplication and successful no-replace publication both verify their
actual winner. Hard publication errors remain failures. Private staging cleanup
does not delete or quarantine another writer's destination.

Independent source review accepted this regular-file publication logic
conditionally and found P1: a FIFO at the digest leaf could block the existing
provider's `open` before its descriptor-type check. The CAS packet alone is not
accepted for unrestricted corrupted-entry handling.

The separate provider correction owns only the POSIX open flags of these raw
bounded-read implementations:

| Owner | Scope |
|---|---|
| `src/runtime/runtime_native.c` | Shared bounded text/byte reader |
| `src/runtime/runtime.c` | Compatibility bounded text reader |
| `src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs` | Shared bounded text/byte reader |
| `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` | Bounded text/byte open helper |

Add `O_NONBLOCK` before the existing same-descriptor regular-file test. The
Pure-Simple facade delegates this open to its provider, so a facade `lstat`
precheck would introduce a race instead of repairing the kernel operation.
The change must preserve existing errors, descriptor closure, no-follow and
oversize refusal, empty files, and Unicode/NUL byte behavior. No general Rust
or vendor changes are included.

## Evidence and remaining gates

| Evidence | Status |
|---|---|
| CAS source-contract and diff checks | PASS, source only |
| CAS working/staged direct-env-runtime guards | PASS |
| CAS eleven private-root executable scenarios | Authored, UNRUN |
| CAS companion manual | Authored, docgen UNRUN |
| Initial CAS source review | Conditional regular-file acceptance; FIFO P1 identified |
| Four-provider flag correction | Authored; source diff/scope checks PASS; independent ACCEPT_STATIC |
| Combined independent source review | ACCEPT_STATIC; no remaining P0/P1 in the reviewed source scope |
| Native C-provider bounded FIFO ABI regression | PASS, 14/14 cases, exit 0 |
| Compatibility C-provider bounded FIFO ABI regression | PASS, 7/7 cases, exit 0 |
| Rust-provider execution | UNRUN; source parity reviewed only |
| Qualified compiler/lib/MCP/LSP and native smoke | UNRUN |
| C ABI harness resources | Native 0.14 s / 1,624 KiB max RSS; compatibility 0.07 s / 1,636 KiB |
| CAS publication latency/memory and branch coverage | UNRUN |

The FIFO regression must invoke the actual provider ABI with a real privately
created FIFO that has no writer. A timeout must terminate and reap a stuck
pre-fix child, so the negative does not hang its caller. Source pattern checks
or a separate implementation of the open algorithm are not runtime evidence.
Provider selection and native versus text-only harness modes must be recorded.
No standalone native build or seed test is authorized by this report.

The authored `src/runtime/test/rt_bounded_read_fifo_selfcheck.c` supplies child
SIGALRM and independent parent monotonic deadlines with kill/reap. Its seven
private-root cases cover positive/zero-bound FIFOs, exact UTF-8/NUL bytes, empty
content, oversize, symlink and directory refusals. The native provider runs both
text and byte lanes (14 cases); the compatibility provider uses `TEXT_ONLY`
(7 cases). Root executed both lanes successfully against the immutable reviewed
source commit. Rust provider changes have source parity evidence only; the C
harness does not qualify Rust execution.

Independent reviewer `/root/astra_warning_authority_review` accepted the combined
source packet after checking the exact four-provider diff SHA-256
`b133d929cc7d0f531046b39599fca4255697d6b9285947b65a0781713e7faeb6` and actual-provider
selfcheck SHA-256 `aed2b1d12eb8187ee0aec63b7b503ff4b6fde8f701d71577afbec6fb855edb6f`.
The reviewer confirmed the original CAS source hash remained unchanged. The
FIFO P1 is resolved at source and the two C-provider ABI lanes now have executed
kernel evidence. The Simple `cas_put` scenarios remain unexecuted.

Root qualification used two bounded cycles. Cycle 1 compiled the real native
provider and harness successfully, then stopped when the compiler-selected
`mold` linker requested an 8 GiB reservation under the unchanged 1 GiB limit.
No runtime test ran in that failed cycle. Cycle 2 explicitly selected GNU
`ld.bfd`, reused the exact successful objects, and ran native 14/14 and
compatibility 7/7 with all hash/link-attribution checks passing. Original failure
logs were preserved; green compilation and tests were not replayed.

Full evidence is retained at `/tmp/simple-fifo-abi-aa5cb90.gIMNVC`; the durable
execution summary and receipt hashes are in
[the execution report](canonical_cas_fifo_abi_execution_2026_10_19.md).

Until the remaining qualified runtime evidence is admitted, do not claim the
combined CAS path is ready for release. External header/receipt/provenance checks remain required even after
both fixes; publication of candidate bytes does not establish provenance.

Related canonical defect and authored scenarios:

- `doc/08_tracking/bug/canonical_cas_publication_unverified_winner_2026_10_19.md`
- `doc/08_tracking/bug/bounded_regular_read_fifo_open_2026_10_19.md`
- `test/01_unit/compiler/cache/cas_publication_integrity_spec.spl`
- `doc/06_spec/01_unit/compiler/cache/cas_publication_integrity_spec.md`

No rejected executable, source439 generation, shared/live cache, or frozen main
build was touched to produce this source packet.
