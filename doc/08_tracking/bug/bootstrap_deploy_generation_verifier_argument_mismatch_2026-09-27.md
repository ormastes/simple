# Bootstrap deployment rejects valid generations at the Stage 3 verifier boundary

Status: source fix implemented; focused wrapper regression passes. Full bootstrap and deployment remain unverified.

## Evidence

At base revision `664c80efda56bbb6903e4e427434e755cb430094`,
`scripts/bootstrap/verify-bootstrap-deploy-generation-authority.shs` passes
three arguments to `bootstrap_stage3_verify_manifest`. Its implementation in
`scripts/check/lib/bootstrap-stage3/manifest-verify.shs` accepts only six or
eight arguments. Any publication or rollback that reaches this final check
therefore fails. The Stage 4 provenance verifier has a separate three-argument
contract, which the wrapper already follows.

This defect is independently confirmed from current source. No retained log
was found tying it to the earlier reported bootstrap failure, so it does not
establish why an admitted source-matched runtime is currently unavailable.

## Change

Pass the manifest path and display path, repository root, parent compiler path
and display path, and the adjacent `.authority-map.env` path. The verifier's
authority checks are unchanged.

## Verification

`sh scripts/check/check-bootstrap-deploy-generation-authority-contract.shs`
passes for publication and rollback. The controlled boundary fixture requires
the exact six arguments and confirms that missing maps, rejected Stage 3
provenance, and rejected Stage 4 provenance still fail. It is a wrapper contract
test, not compiler or provenance admission evidence.

No further full bootstrap was run: this session had already reached the
repository's three-cycle bootstrap verification limit. The next eligible
bootstrap session must produce and admit a source-matched runtime before
parser, dynload, or SimpleOS product test results can be claimed.

## Host and capsule limitations confirmed during review

The real verifier still requires Linux `/proc/<pid>/fd/<fd>` reopen semantics.
For an ordinary on-disk map, `manifest-verify.shs` opens descriptor 9 and hashes
it through `/proc/<pid>/fd/9`; later map and manifest snapshots also use this
protocol. A focused real-verifier probe on Darwin with an existing regular map
rejected at `manifest-entry-bound-map-hash` before reading map content. The
six-argument correction therefore does not unblock macOS deployment. The
verifier's existing header explains why replacing these read paths with
`/dev/fd` would be incorrect: duplicate descriptors share their read offset.
The historical Darwin protocol bug document referenced by that header is
absent from this checkout.

`BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE=1` additionally requires eight verifier
arguments and descriptor-bound facade modules. Current production assignments
to that flag occur in the Stage 3 child verifier and generated capsule; they
do not change the normal deployment parent environment. The deployment wrapper
always selects the on-disk facade, so injecting capsule mode into its environment
already fails facade admission before either Stage 4 or Stage 3 verification.
Supplying two invented parent arguments or clearing capsule mode would not make
that a valid descriptor invocation. This fix retains normal on-disk invocation
and does not add descriptor-capsule deployment support.

Next source work for Darwin must provide a reviewed authority protocol with
independent repeated reads, retained file identity, and parent/helper descriptor
binding across the verifier and its producers. That is a separate protocol
change; a pathname fallback must not bypass existing authority checks.

The required change spans `manifest-verify.shs` (map snapshots on descriptors
9/7, manifest snapshot on descriptor 8, runtime directory on descriptor 6),
`manifest-write.shs` (bound-map identity producer), `authority.shs`
(descriptor-map validation), `bootstrap-stage3-provenance-verifier.sh`, and
`bootstrap-stage3-shared-runner.pl` (parent-owned helper/source descriptor
transport). Several paths also call GNU `stat -Lc` for device, inode, mode,
and size. Fixing only the first map hash would leave those later barriers.

A safe portable owner must preserve independent read positions and stable
device/inode/mode/size identity, including after unlink or pathname replacement.
Focused acceptance tests for that owner must include repeated complete reads,
replacement and symlink rejection, mutation during snapshot, closed/wrong
descriptor rejection, helper binding, and mismatched parent source/git receipts.
The existing controlled wrapper fixture cannot establish these properties.
No protocol implementation was attempted in this bounded repair because an
isolated path substitution cannot satisfy that authority contract.
