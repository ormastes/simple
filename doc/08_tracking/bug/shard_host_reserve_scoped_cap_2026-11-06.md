# Host reserve consumed the scoped compiler cap

Status: repair verified with a native bootstrap fixture; Phase 3 admission remains incomplete.

The mirgen2 Phase 2 compiler linked 1592 modules, then its `p2_add` sanity build
failed worker admission. Its retained failure evidence is
`/home/yoon/dev/simple-mir-generic-boot/build/bootstrap-mirgen2/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env`;
producer SHA256 `ffe83fd87c69573a1ca93e24134e46bbe754be7dff2de2f0eeefc4cf60c9037a`
is retained as `stage2/aarch64-unknown-linux-gnu/simple.rejected`.

The observed arithmetic was a 25,165,824 KiB tree cap, 97,608,600 KiB host free,
and a 25,165,824 KiB host reserve, yielding zero admissible memory. The old
helper selected the cap instead of host free before subtracting the reserve.
This also ignored a genuinely low host-free measurement when a larger cap existed.

`config/host/host_config.sdn` and `doc/07_guide/infra/toolchain/host_config.md`
define `mem_reserve_free_mib` as RAM/commit kept free on the host. The repair
therefore bounds known-free admission by `min(declared, cap, host_free - reserve)`.
With unknown host free, the conservative existing `cap - reserve` fallback
remains. The enforcing cap, parent reservation, worker estimates and refusal
of insufficient worker capacity are unchanged.

## Native verification

`test/fixtures/bootstrap/host_reserve/main.spl` imports the production helper
and performs eight real value checks. The unchanged fixture failed with exit 1
before the repair and passed all eight checks with exit 0 afterward. Cases cover
real mirgen2 inputs, low host free, reserve exhaustion, a tighter declared cap,
unknown free, no cap, no measurements and an explicit larger reserve.

The producer was the immutable opus10 Phase 2 snapshot SHA256
`43f9a6fc68ac232fcb3d28b0a28ada8fba5b04f5e16326e8f122d09208671c5f`, with its matching
runtime capsule, Cranelift, `core-c-bootstrap`, explicit
`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`, and a private sequential native cache.
This is bootstrap-scoped native executable verification, not a full CLI test
runner pass or producer admission. The existing SSpec was extended but was not
executed through an unavailable self-hosted test CLI.

Evidence directory:
`/home/yoon/dev/simple-bootstrap-host-reserve-20261106/build/bootstrap-host-reserve/`.
It retains before/after build and execution logs, exit statuses and binaries.

- Before binary SHA256: `e15a41f5b2bbd3519539735b574ea604990a608d4e7beaf9c4cdff786f8c970a`
- After binary SHA256: `ab75a056c9488db9fdf1d02e6a166ec4cb23fa91f3c40354e46b903fe0ef74f7`
- Working and staged facade guards: PASS.

The corrected effective budget is 25,165,824 KiB. The separate parent reservation
and 9,000,000 KiB worker estimate still admit only one worker under that cap;
the current per-file pool requires two. This repair alone does not unblock
mirgen2 admission, does not reduce reserve configuration, and does not justify
starting Phase 3 from the rejected candidate.
