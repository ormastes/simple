# Seed interpreter cannot guarantee zeroization through a parameter

Status: OPEN, accepted limit of the Phase 1 seed. Severity: P2. Date: 2026-10-31.

## Symptom

Under the Phase 1 seed interpreter, a wipe function can report success while the
caller's array keeps its bytes. The wipe's readback checks the callee's copy, so
its `true` result proves nothing about the owner.

Measured with `SIMPLE_EXECUTION_MODE=interpret` on seed SHA-256
`55be5e48ecd717a59cd7f0538768b22bbc832669025571c546d30fdf817dc0ec`:

| Array built with | Byte after callee wipe |
| --- | --- |
| `o.push(128u8)` (literal) | 128, write lost |
| `o.push((128).to_u8())` (computed) | 0, write visible |

The same difference decides whether a `StorageReadView.image` or
`CodecSessionV1.secret_material` owner is wiped. Fixture
`test/fixtures/devhub/fresh_secured_db/main.spl` failed at
`direct session close wipe` on real derived key material.

## Cause

Interpreter arrays are copy-on-write. `exec_assignment`
(`src/compiler_rust/compiler/src/interpreter/node_exec.rs`) writes in place only
when the `Arc` is unique, and otherwise clones with `Arc::make_mut` to preserve
value semantics. A callee's write to a shared array therefore lands on a private
copy. Why the computed form stays visible was not established.

## Decision

Seed array semantics are unchanged: the seed is bootstrap-only, and the change
would affect all interpreted code. Wipe guarantees are judged natively.

- `test/fixtures/devhub/native_storage_wipe_alias/main.spl` holds the owner claim
  that was in `storage_port_spec.spl`. On Phase 2 the original array was wiped and
  `val alias = image` was not, so the alias claim was dropped.
- `fresh_secured_db` prints `UNVERIFIED wipe checks` when
  `DEVHUB_FRESH_SEED_INTERPRETER=1`. Native runs always enforce the checks.

Do not cite a Phase 1 run as evidence that secrets or plaintext were erased.
