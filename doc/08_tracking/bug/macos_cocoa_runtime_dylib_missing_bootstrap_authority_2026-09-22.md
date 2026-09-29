# macOS dynamic Cocoa provider omitted from bootstrap authority

Status: source fixed and contract tests pass; full bootstrap pending.

The macOS Cocoa ABI must live in the runtime dynload library. Existing bootstrap
seed tuple projection intentionally excluded the runtime cdylib, and Phase 2
runtime capsules copied only native-all/backfill archives and the hosted rlib.
Moving Cocoa implementation out of the duplicate static providers alone would
therefore leave downstream consumers without the admitted dynamic provider.

Canonical generation and legacy migration now pass the target explicitly.
For an Apple Darwin target, the atomic seed tuple requires and freezes
`libsimple_runtime.dylib`. The complete directory snapshot already binds that
additional member to generation publication. Other targets retain their
existing tuple. Optional target arguments retain compatibility for existing
legacy test callers; production callers provide the target.

Runtime capsule publication copies the admitted dylib, checks source/copy
hashes, and binds `dynamic_runtime_sha256` into the capsule aggregate identity.
Verification rejects changed, missing, unbound, writable, or symlinked providers.
Legacy no-dylib v1 capsules retain their original aggregate format.

Regression evidence lives under
`build/evidence/macos-enforced-bd544/cocoa-authority/` in the isolated bootstrap
checkout. Extended `bootstrap_stage3_seed_tuple_projection_test.shs` and
`phase2_runtime_capsule_contract_test.shs` pass. The latter fails with the parent
capsule publisher because the macOS dynamic runtime is missing. The tuple
uses existing 1 MiB streaming copy/hash buffers; the capsule uses streaming
hash commands and file copy, with no artifact-sized in-memory buffering.

Actual Cocoa symbol exports, ABI signatures, and consumer loading are verified
separately by the Cocoa runtime owner. These projection tests do not claim
native Cocoa execution or full bootstrap completion.

The bootstrap invokes that owner's artifact checker against the frozen pair
before Stage 2, resolving `llvm-nm` from pinned `LLVM_CONFIG --bindir` and using
the canonical 60-second process timeout. The focused gate test executes the
actual shell block and proves macOS routing, exact frozen paths, preserved tool
path spaces, non-macOS absence, and rejection of missing/relative tool paths.
Its log is `cocoa-authority/gate-positive.log`; the test mocks only the external
checker dispatch, so real artifact proof remains separately required.
