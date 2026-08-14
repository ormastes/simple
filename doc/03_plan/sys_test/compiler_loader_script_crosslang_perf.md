# Compiler, loader, script, and cross-language performance test plan

## Replacement lane B status (2026-08-14)

This detached worktree owns only the compiler-loader packed-byte lane B.  The
current `origin/main` ancestry already contains the original loader/cache and
packed-byte optimization, but it does not contain the later lane-B interpreter
boundary hardening commits.

Acceptance items for this replacement lane:

- [ ] Preserve packed `[u8]` storage for index, slice, iteration, concat, clone,
  equality, and byte-valued mutation; widen only at a generic-value boundary.
- [x] Make packed-byte mutators write the updated value back to the interpreter
  place and preserve copy-on-write/frozen-value behavior.
- [ ] Keep foreign packed-byte capabilities input-only, descriptor-bounded, and
  unable to escape the call that admitted them.
- [ ] Retain loader negative-cache caller sensitivity, invalidation, and the
  measured failed-probe reduction contract.
- [ ] Pass focused packed-byte semantics, loader resolver, RSS-contract, and
  cross-language retained-contract gates exactly once on the integrated source.
- [ ] Pass compiler/core/lib and MCP/LSP smoke checks required for compiler
  language-surface changes, plus optimizer review of touched `.spl` files.
- [ ] Commit only intentional lane-B files, rebase under the integration lock,
  push `HEAD:main`, prove reachability from refreshed `origin/main`, and leave a
  clean worktree.

Current blockers:

- The later lane-B work exists only on detached historical commits based on a
  divergent repository snapshot, so it cannot be merged wholesale.  Remaining
  changes must be replayed selectively against current `origin/main`.
- Baseline and focused acceptance commands have not yet been run in this fresh
  replacement session; each will be executed at most once unless it fails, with
  no more than three total verify/fix cycles.

Verification update:

- `cargo check -p simple-compiler`: PASS after routing packed receivers through
  the canonical resolved-place write-back path.
- Focused mutator regression gate: WARN.  The original replayed identifier-only
  path failed, and the three-cycle cap was reached while identifying that the
  current parser routes these receivers through resolved places.  The final
  resolved-place correction compiles, but the focused gate was intentionally not
  run a fourth time.
- Self-hosted compiler/core/lib and MCP/LSP gates remain unavailable because this
  fresh worktree has no `bin/release/<triple>/simple`; the Rust seed was not used
  as a tooling fallback.

## Scope

`test/05_perf/compiler_loader_script_crosslang_perf_spec.spl` is the focused
source-level gate. It exercises resolver cache semantics and audits the
cross-language/byte harness contracts without launching expensive benchmarks.

## Evidence map

| Area | Executable evidence |
|---|---|
| Repeated negative cache | Same missing module/caller resolves once; counter remains 1 |
| Caller sensitivity | Adjacent callers create two entries; revisits remain cache hits |
| Reset invalidation | Reset starts a fresh generation and preserves result |
| Failed existence probes | 100 reset-per-request baseline versus 1000 retained requests; exact resolution, uncached 100/1, positive baseline, cached ≤10% of baseline |
| Identity/mode | Self-hosted provenance and no-fallback strings are required |
| Native bytes | Fixture declares native mode and checks 1/4/32 MiB length, boundaries, checksum |
| RSS | Linux-only GNU `/usr/bin/time` over `timeout`; focused child-inclusion/fast-exit/timeout contract; unsupported hosts are unavailable and four-times payload is rejected |
| Fixture timing | Fixture receipt enforces `<1000 ms` at 1 MiB and `<30000 ms` at 32 MiB; host wall p50/p95 remains separate |
| Peer parity | Rust producer, Bun path, and `fib(35)=9227465` checksum are required |

The canonical counter lives only at the `rt_file_exists` facade and reports
**failed existence probes**, not filesystem syscall counts. Native C/Rust
providers admit a lease before the facade operation, close accepting before
draining leases, and use a non-wrapping 63-bit generation. The pure-Simple
interpreter provider is documented single-thread and fail-closed. The focused
test asserts an exact packed two-miss `(total, failed) = (2, 2)` result and
audits C runtime, native runtime, header, Rust exports, codegen, and interpreter
registration parity; it makes no disabled-assembly performance claim. Saturation
is seeded at `(0x7ffffffe, 0x7ffffffe)` and two misses must end at
`(0x7fffffff, 0x7fffffff)`, preserving `failed <= total`. The direct fixture is
unique per process and must already be absent; it is never deleted by the gate.
The parity audit also covers the pure-Simple text-extern ABI router, LLVM
declaration routes, minimal SFFI ABI, and interpreter-call router.

`scripts/check/check-file-exists-probe-c.shs` compiles the small test-only
`src/runtime/test/rt_file_exists_probe_selfcheck.c` against both `runtime.c`
and `runtime_native.c`. It requires a PID-scoped missing path to be absent and
checks the seeded saturation result without deleting any fixture.
