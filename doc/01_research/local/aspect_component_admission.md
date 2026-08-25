<!-- codex-research -->
# Local research: checked aspect-component admission

Date: 2026-08-25. Status: source audit only; no tests or builds were run.

The repository already has substantial Pure Simple machinery: SMFAPK1 pack and
catalog parsing in `src/lib/common/aspect_pack.spl`; `.aspect_pack` SMF emission
in `src/compiler/70.backend/linker/smf_writer.spl`; registration, catalog
invalidation, and generation-aware references in
`src/compiler/99.loader/module_loader_compat.spl`; checked dynSMF admission and
the default manifest in `src/os/smf/dynsmf_session.spl`; and app-root checked-config routing in
`src/app/main.spl` and `src/app/startup/dynsmf_autoload.spl`.

The missing production edge is ownership and identity. A reference search found
pack/catalog builders, the standalone producer, and `moduleloader_*aspect*`
APIs called by definitions/specs but not a product entrypoint. The default
manifest in `src/os/smf/dynsmf_session.spl` has no explicit aspect-pack
component or catalog path/digest contract. The common resolver in
`src/lib/common/structural/component/descriptor.spl` and dynSMF planner in
`src/os/smf/dynsmf_session.spl` use different identities and stale-static
rules. `src/lib/common/facet_syntax.spl` is a string parser, not compiler
lexer/AST/HIR/MIR lowering.

The smallest coherent slice is therefore one checked aspect component selected
by the canonical component resolver, admitted by exact identity and digest, and
registered into one persistent `ModuleLoader`. Static selection performs no
open; dynamic startup selection performs one checked open; every failure leaves
catalog and loader state unchanged. Automatic packaging and typed facet syntax
remain later, dependent slices.

Research sidecars: three GPT-5.6 Sol xhigh read-only audits covered component
resolution, pack/facet implementation, and documentation traceability. Final
option synthesis is by the primary model.
