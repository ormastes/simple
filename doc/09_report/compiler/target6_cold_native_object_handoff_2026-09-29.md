# Target 6 cold HIR/native object handoff (2026-09-29)

Status: focused production-path handoff; the archive-backed V3 publisher and
full entrypoint cutover remain open.

The driver already captured frozen-inventory typed HIR receipts before HIR
eviction. Its native output loop now records the module-to-object path after
the existing capsule receipt check accepts a fresh or cached object. The map
is empty on warm and non-SCV builds and is reset alongside typed receipts on
a new cold capture. It retains paths, not object bytes, so the later archive
producer can verify and persist actual codegen outputs without increasing
the driver's retained object-byte set. No time/RSS improvement is claimed.

Focused evidence from the isolated Target 5/6 worktree:

- Pure-Simple Stage-2 compiler SHA-256:
  `d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
- `SIMPLE_NO_STUB_FALLBACK=1` entry-closure native build of
  `test/fixtures/compiler/cold_hir_native_object_handoff_probe.spl`:
  691 units compiled, none failed. It linked against the explicit hosted
  runtime archive. The 2,851,520-byte executable has SHA-256
  `579003548cd37580759e58020ac40f368bdeed311b7c9261c7fbae2b6eadf649`.
- Native execution exited 0 and printed
  `PASS cold_hir_native_object_handoff_probe`. It checks that a warm context
  retains no path, empty identities fail, one cold path is retained, and a
  duplicate cannot replace that binding.

The existing `native_capsule_result_receipt_spec.spl` fixture segfaulted
with an invalid array handle both with the added handoff scenario and at
the original committed revision, under the same Stage-2 compiler and hosted
runtime. That fixture supplies no pass verdict for this change. The focused
probe is the executable evidence for the new handoff. The reset added after
the probe's build has source review and `git diff --check` evidence only; it
needs runtime coverage in a later verification session.

Next: derive and verify object digests from these recorded paths, persist the
actual object/archive bytes with typed HIR and action receipts, publish the
scoped V3 graph only after archive readback, then prove correct warm linking
and paired cold/warm p95 and RSS on a production fixture.
