# Provider composition and positive lifecycle acceptance supplement

Status: proposed implementation contract; NOT IMPLEMENTED by this document.
All runtime, generated-manual, native-loader, coverage and performance evidence
is UNRUN. Full item 4 remains FAIL/incomplete. This supplements the retained
item 4 design and pack transport design; it does not remove other formats,
bounded execution, lifecycle, dependency admission or platform obligations.

Owner/session: `/root/linker_research`, `item4-provider-positive-docs-20261004`.
Worktree: `C:/dev/simple-item4-provider-docs-20261004`; branch
`work/item4-provider-positive-docs-20261004`; inspection base/expected release
target: `f5fec9ccf8cba4287dd83f8032c4f59dd944838a`. Docs-only ownership;
integration owner `/root`; sidecars N/A. Active root, acceptance and runtime
agents and the separate locked SHA-owner worktree were observed; none is edited.

## Source-backed gap

`src/compiler/70.backend/linker/linker_pack.spl` already admits a real dynamic
provider, queries/pins its CLI interface and invokes `linker-v1` with checked
request/policy/receipt transport. `linker_lifecycle.spl` retains old generation
pins, replaces providers, collects retired mappings and keeps static recovery.
These operations are not called from the production native-build CLI.

`src/compositions/linker_fast/composition.spl` and the bounded counterpart each
seal one engine descriptor with no required facets. Their literal composition
digests are not an actual artifact/operation binding. A successful descriptor
seal alone does not establish a complete linker composition or memory behavior.

`item4_linker_pack_native_spec.spl` loads the mapped provider but sets architecture
999 and expects UnsupportedFeature for every dispatch. It proves no successful
link. The manual prerequisite shared artifact is also not executed evidence.

## Production call sequence and ownership

1. Extend the existing native-build argument/config owner with explicit static
   recovery versus manifest-selected optional pack choice. Exact flag spelling
   belongs to CLI design review; do not add implicit discovery, downloaded packs,
   changed default fallback, or new selected requirement scope.
2. Add one `linker_composition.spl` owner. Resolve the selected manifest, validate
   independently registered schemas and artifact identity, build the actual
   engine/relocation/byte-source/layout facet graph, and call the existing sealer.
   Required facets must reflect real operation dependencies. Bind the seal's
   generation, facets and composition digest to the selected operation owner.
3. Create one mutable `LinkerLifecycleV1` with independently retained static
   `link_request_to_native` recovery. Admit the selected pack through
   `publish_pack`; only successful admission may replace the active generation.
4. For each native-build link job: validate request/policy, open a session, invoke
   the pinned generation, close the session on every returned outcome, and retain
   failed cleanup owners. Return the real receipt and produced artifact. A
   returned failed-link receipt is distinct from transport/admission failure.
5. Replacement retires the old generation; collect only after its last pin is
   released. Shutdown must close sessions, retire the active dynamic generation
   to static recovery, collect mappings and retry retained failed admission
   cleanup without losing ownership. No process-global mutable singleton.
6. Dispatch selection occurs above `link_request_to_native`. The provider-side
   `linker_pack_command.spl` continues calling that adapter directly, preventing
   recursive pack selection inside the mapped provider. Static recovery must
   not require publication capacity, a pack loader or a fresh session.

All mutating owner operations use `me` and named `var` receivers. Array/Option
owner extraction requires explicit writeback before propagating failure.
Preserve existing external engine fallback semantics and truthful selected-engine
receipts; pack identity is composition metadata, not a replacement engine name.

## Manifest and trust inputs

The application-selected, independently admitted manifest supplies provider ID,
artifact path/kind, expected artifact digest, host ABI interval, interface major/
minor and ABI digest, capability grants/requirements, registered schema
requirements, composition/facet binding, host/target support and policy digest.
Expected identity must not be synthesized by hashing whatever file happens to
exist at the requested path. Tests may hash their independently built fixture
to arrange a fixture contract; that is not production trust admission.

The existing query reports zero provider/implementation identity digests. Do not
treat those fields as proof of manifest provenance. Bind verified loader artifact
identity and registered composition identity explicitly; specify and implement
any required query identity strengthening before calling it an attested binding.

Before/after pathname hashes do not establish immutable mapped bytes or transitive
dependency identity. Signed closure, hostile-path snapshot, platform loader trust
and capability enforcement remain separate required admission work. This
supplement does not authorize bypassing them. A Fast successful-link slice is
useful while bounded mode remains UnsupportedBudget until actual parent-owned
resource enforcement and accounting exist.

## Six executable positive acceptance scenarios

Use canonical `std.spec.step` and `item4_provider_*` helpers. Missing admitted
native runtime/provider/host prerequisites are explicit failures or UNRUN evidence,
never replacement callbacks, canned PASS or claims based only on source text.

| ID | Real setup/action | Independent output and owner oracle |
|---|---|---|
| PACK-POS-001 CLI path | Build the real exported pack entry, select its checked manifest through native-build CLI, link checked-in host-compatible entry/provider objects | Output exists and independently decodes to the expected machine, entry, load permissions, relocation bytes and fixture data; receipt names actual engine/host/target/policy; host run checks expected result where admitted |
| PACK-POS-002 replacement | Load independently identified pack artifacts A and B; pin A, publish B, open B, link the same fixture through each to separate outputs | Both outputs decode and match independent fixture values; session handles bind distinct generation/composition identities; A's operation remains callable after B publication |
| PACK-POS-003 retirement | Attempt collection with A pinned; then close A and collect, retaining B's pin | Pinned collection fails without removing A; post-release collection succeeds, stale A handle fails, B performs another successful fixture link; native loader ownership shows A unmapped only after release |
| PACK-POS-004 capacity recovery | Fill generation and session tables with genuine pinned owners, then invoke retained static recovery on real objects | Recovery produces a valid independently inspected image and actual static engine receipt despite failed publication/open; it never calls the dynamic provider; release all original owners afterward |
| PACK-POS-005 failed replacement | Publish good A, attempt B with independently wrong artifact/ABI/manifest identity, then link again through A | A still produces correct output and unchanged active generation; failed candidate cleanup completes or remains explicitly retained for retry; sentinel destination remains unchanged by rejected admission |
| PACK-POS-006 sealed binding and shutdown | Construct/seal the real required facet graph, run a successful link, then shut down the owner | Seal bindings match manifest provider/artifact/composition identities and selected facets; output oracle succeeds; sessions/pins/mappings/pending cleanup drain, second shutdown is defined, later dispatch rejects closed owner |

These scenarios supplement existing malformed-wire and refusal scenarios. Check
setup bounds before mutation/indexing because `expect` does not abort execution.
Use independent ELF/PE/Mach-O field readers and known fixture answers; comparing
two calls to the same linker alone is insufficient. Loader unload observation
must use existing authoritative loader state/handles, not a local boolean.

## Delivery boundaries

Author tests before implementing composition owner and CLI integration; no
observed RED/GREEN is claimed without an admitted runner. Keep six scenario
manuals traceable to real `step` flows and generate them through canonical tooling
when available. Parent owns common plan, CLI/native wrapper integration and final
review. Source slices can land separately with explicit open gates; no release
tag, publication or full completion follows from this document.

Semantic identity prerequisite clarification (release `d8680fe6ec21`): the
declaration semantic issuer boundary mentions the canonical stream only in
future-integration comments and remains unavailable pending five live
capabilities. It is not a current production caller or an available manifest
authority source. Repairing SHA/canonical-stream ownership does not activate
that boundary or supply the independent manifest trust required above.
