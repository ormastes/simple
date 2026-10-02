# Shared parse cache acceptance matrix

Overall status: **BLOCKED; no production deployment authorized by evidence**.
The user authorized deployment once both hosts verify; that condition remains unmet.

| Case | Requirement | Executable/check | Windows | Linux |
|---|---|---|---|---|
| Equal portable key; target-dependent cfg differs | 001 | `shared_parse_cache_boundary_spec.spl` | UNRUN | UNRUN |
| Real flat-pool hydration, literal 73, state reset | 002 | same SSpec | UNRUN | UNRUN |
| Digest-valid malformed pools reject and reparse | 002 | same SSpec | UNRUN | UNRUN |
| Source/input/parser/features/cfg/namespace mismatch | 001 | same SSpec plus actual probe negatives | UNRUN | UNRUN |
| Corrupt/truncated/key/envelope/codec rejection | 003 | same SSpec plus copied real cells | UNRUN | UNRUN |
| Traversal and private artifact namespace rejection | 004 | same SSpec | UNRUN | UNRUN |
| Source/cell/root symlink or reparse rejection | 004 | existing root test plus native probe | UNRUN | root preflight only |
| Missing/wrong/mutated sealed authority | 005 | native probe and actual compiler fallback | UNRUN | root preflight only |
| Windows STORE -> Linux HIT + semantic hydration | 001/002/005 | compiled crosshost probe and cell witness | UNRUN | UNRUN |
| Linux STORE -> Windows HIT + semantic hydration | 001/002/005 | second fresh logical source path | UNRUN | UNRUN |
| Concurrent identical publication/idempotence | 006 | two concurrent compiled probe workers | UNRUN | UNRUN |
| Conflicting publication and interrupted temporary | 006 | production store API + isolated root | UNRUN | UNRUN |
| Foreign private frontend/HIR/native generation | 007 | production loader rejection + scope receipts | UNRUN | UNRUN |
| Native object format; handles/session/local-path isolation | 007 | host artifacts + owner manifests | UNRUN | UNRUN |
| Deploy and cold-private post-deployment smoke | 008 | compiled manager/worker SOSIX route | BLOCKED | BLOCKED |

## Bounded native protocol

1. Reserve capacity with the manager owner. Budget: manager 4 GiB, Linux proof
   2 GiB, Windows proof 7 GiB when separately admitted, host reserve 8 GiB.
   Do not resume the held legacy dispatcher or bypass capacity through a shell.
2. Build `test/fixtures/compiler/shared_parse_crosshost_probe.spl` with the
   admitted self-hosted compiler for each host. The fixture imports production
   frontend code; a compiler that only passes a hello cannot qualify it.
   Retain compiler/runtime/source SHA, command, SOSIX host/process receipt,
   exit, peak memory, elapsed time and resulting native image SHA.
3. Freeze a source tree containing its full parser subset and
   `examples/10_tooling/shared_parse_cache_value.spl`; seal its file-hex authority.
   Use LF source bytes. Freeze a second logical fixture with identical source
   bytes for reverse direction. Never mutate the sealed snapshot in place.
4. Configure fresh, distinct private cache roots/scopes and the receipt-pinned
   shared root. Set probe mode `publish` for producer, `consume` for consumer;
   each run is a new native process. The consumer must have no private entry.
   SOSIX's root receipts must prove canonical non-overlap, including mount and
   reparse aliases. The probe's lexical slash/case/nesting guard is insufficient
   to establish physical isolation by itself.
5. Require producer STORE and consumer HIT for the exact same key, immutable
   cell SHA and payload SHA. The compiled probe additionally validates the
   target receipt and actual AST literal 73. Producer parser-call delta must be
   one, consumer zero. A private-cache hit or RACE_HIT alone cannot prove origin.
6. Repeat reverse direction with its fresh logical path. Cross-host sharing
   requires the same parser source identity, codec and features, while native
   outputs retain their respective host target and producer identities.
7. Copy a genuine cell into isolated negative roots. Independently corrupt,
   truncate, alter codec/address, remove authority or vary one key input. For
   malformed cells use `reparse`: delta one plus the same semantic result.
   Missing/wrong parser authority must fail before the fixture claims success.
   Do not corrupt, delete or evict production data to run negative tests.
   The fixed-source compact probe cannot execute every source/cfg/parser
   mutation: its literal oracle rejects changed source, and it derives parser
   identity instead of accepting a caller override. Those rows require
   additional frozen source fixtures or an actual compiler run with a new
   sealed parser snapshot. A fixture-input panic is not cache-miss evidence.
8. Run the remaining actual concurrency, interruption, no-follow and private
   generation cases. Retain loser/winner outcomes and artifact hashes. These
   remain mandatory even if the compact SSpec is green.

## Staged configuration (not applied)

Both hosts require `SIMPLE_SHARED_PARSE_CAS_ROOT`,
`SIMPLE_SHARED_PARSE_SOURCE_ROOT`, `SIMPLE_SHARED_PARSE_SOURCE_AUTHORITY_PATH`,
`SIMPLE_SHARED_PARSE_SOURCE_AUTHORITY_DIGEST`, `SIMPLE_FRONTEND_CACHE=1`,
`SIMPLE_FRONTEND_CACHE_SCOPE`, `SIMPLE_FRONTEND_CACHE_DIR`, and trace enabled.
`SIMPLE_BOOTSTRAP=1` is incompatible with this proof. The probe derives parser
identity through the production sealed-authority owner; do not inject a digest
as a substitute for source admission.

Probe-specific inputs: `SIMPLE_SHARED_PARSE_PROBE_MODE`,
`SIMPLE_SHARED_PARSE_PROBE_SOURCE` (absolute frozen source filename), and
`SIMPLE_SHARED_PARSE_PROBE_TARGET` (actual host target triple). Scope and private
root differ for every cold run. The manager wrapper takes the explicit
`--shared-parse-cas-root`/`SIMPLE_BOOTSTRAP_SHARED_PARSE_CAS_ROOT` admission input.

Proposed shared root: `D:/dev/simple-shared-parse-cas-v1`, Linux spelling
`/mnt/d/dev/simple-shared-parse-cas-v1`. These spellings are not themselves
identity proof; bind them to the manager's pinned real-root receipt.

## Current blockers and evidence limits

- The Windows `e7ec89c1...` diagnostic image supports `native-build`, not `run`.
  No 7 GiB fixture build reservation is allocated.
- The Linux `04d72b6a...` image passes a simple LLVM hello but has a known class
  failure. The newer class-fix candidate is blocked at LLVM `rt_alloc(nil)`.
- The manager capacity repair must rebuild manager and both workers from one
  reviewed commit; the old generic worker never launched its task child.
- Qualified SSpec execution and SPipe docgen are UNRUN. The companion manual
  is explicitly authored from source, not a generated-success receipt.
- `D:/dev/win-linux-shared-cache-proof-20261002/deployment.md` and
  `D:/dev/manager-cache-acceptance-20261001/acceptance.md` retain prior evidence.
  Their preflight/synthetic witness checks cannot close the rows above.

Each acceptance check runs once per unchanged candidate; at most three
fix/verify cycles. Retain caches, artifacts and failures. Missing evidence is
BLOCKED/FAIL, never an optional skip or production PASS.
