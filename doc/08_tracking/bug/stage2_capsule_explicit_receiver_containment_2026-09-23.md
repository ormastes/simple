# Capsule identity input transport: explicit receiver containment

Date: 2026-09-23. Baseline: `bb8b358f1d15117d007fa1d47a786c8e9aedcbec`.
Status: scoped native projection PASS; independent Astra review PASS.
Stage2 admission, full compiler tests, and generic omitted-self repair remain OPEN.

## Production change

`FrozenNativeCapsuleConfigV1` groups six scalar options into one record. Four
production callers and seven unit-test callers preserve every original value,
including empty provider receipts and default witness maps. Freeze now takes
six arguments including self. Explicit `self` on capsule identity methods and
the participating context methods binds import arity to instance semantics.
Canonical identity encoding and validation predicates are unchanged.

The earlier rejected Stage2 candidate (SHA-256
`1f89735e5982f6a13c54e92ae874aa68935263d90f6f3e4ee2c6fa6a5604a1b3`)
marshaled only eight of eleven freeze inputs; the provider receipt and both
witness maps were lost. Preserved diagnosis:
`/Users/ormastes/simple-tmp/stage2-capsule-identity-20260922/doc/08_tracking/bug/stage2_capsule_freeze_truncated_arguments_2026-09-22.md`.
Do not generalize this to all calls over eight arguments: the separate
receiver reproducer transported stack arguments correctly with explicit self.
Generic defect evidence is retained in commit
`531bbdab4c4d55b1e0559a820fee849c70744379`; it remains unfixed by this containment.

## Native proof

Fixture: `test/fixtures/native/capsule_identity_transport/README.md`.
Evidence root:
`/Users/ormastes/simple-tmp/capsule-identity-explicit-self-20260923/build/native_probe/capsule-explicit-self`.
One cycle, independent red/green caches, no unresolved-stub fallback.
Both builds exit 0. Red (same config and scenario, omitted freeze self) exits
138. Green exits 0 and prints `capsule-identity-transport-pass`.

The exact canonical text assertion passes with nonempty provider receipt,
module witness, and witness reason. Green rejects backend/target/release/opt
mismatches; provider, witness, reason, source, MIR, storage, and validity
mutation; and an empty provider admission hash. Restoring inputs restores
acceptance. Explicit empty built-in provider/maps also pass.

`red/call.disasm` at `0x100005720..0x100005730` passes five arguments x0..x4.
`green/call.disasm` at `0x100005708..0x100005730` passes receiver plus five
arguments x0..x5, matching the extracted freeze definition. This red isolates
receiver metadata, not an independent scalar-config necessity claim.

The fixture models source/storage providers and MIR/storage serialization;
it does not test real filesystem mutation, real MIR encoding, omitted default
arguments, or full compiler bootstrap. No seed test-suite result is claimed.

## Authority and resources

Bootstrap-only authority:
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority`.
Producer SHA-256:
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.
Runtime archive SHA-256:
`5e11731fa77990ecc170b939d2b16a48a1d9be417069202f365861e69576006d`.

| Variant | Build seconds | Sampled build tree KiB | Run seconds | Run maximum RSS bytes |
|---|---:|---:|---:|---:|
| Red | 2.52 | 194336 | 0.33 | 8781824 |
| Green | 2.37 | 209616 | 0.35 | 9322496 |

All four receipts show observer_errors=0 and quiescent=1 under 5859375 KiB.
Enforcement is sampled (`hard_memory_limit=0`), not kernel containment.
Build/run deadlines were 180/20 seconds. These short runs do not establish
production performance; red aborts early. The config adds one six-field
allocation per freeze call, with no new loops, scans, or cache-policy changes.
Explicit self changes arity metadata without runtime allocation.

Executable SHA-256:

- Red: `e2bcb40f44f4f27471aa22236755a80f48785240875997f414f60e85003bcfd1`.
- Green: `e31cb8fff64a6f300a600e41d90b78f9a3d5a9947208b7951506bd24425543f2`.

This patch requires subsequent Stage2 admission before the source-matched CLI,
test runner, compiler tests and supplemental manifests, and then Stage3.

Independent Astra reviewer inspected all eleven caller migrations, unchanged
freeze body and identity predicates, production extraction, red/green source
difference, four receipts, and both disassemblies. No blocking defect found.
The reviewer confirmed a single 48-byte config allocation outside the capsule
loop and accepted the modeled-dependency and omitted-default limits above.
No green tests were rerun for review.
