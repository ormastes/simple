# Stage 2 loses cross-module codec result field types

Status: provider workaround applied; compiler fix remains open — p3fix-lane
BLOCKED with verbatim canary grant, see 2026-11-11 addendum below.

Admitted compiler:

- path: `/mnt/data/bs2/final-e73-run2/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
- SHA-256: `2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`
- sanity evidence: `status=pass`

Reproduction: compiling `src/app/provider_cli/native_provider_v1.spl` through
the admitted `native-build --entry-closure --emit-archive --no-mangle` path
failed while accessing `.ok` on the result of
`encode_provider_query_result_v1`:

`hir: Unsupported feature: cannot infer field type ... struct
'ProviderQueryWireWriteV1' field 'ok'`

Explicitly annotating cross-module codec results is the safe provider-side
fix. The compiler should eventually preserve the declared return type through
cross-module calls without requiring redundant local annotations.

## Triage 2026-11-11 (p3fix lane boot24)

**Verdict: BLOCKED (verbatim canary grant). Fresh re-verification at tip
6233df4b9f9ea.**

Fresh source state this pass:

- The provider-side annotation workaround is still in place
  (`src/app/provider_cli/native_provider_v1.spl:46-112` — explicit
  annotations around `encoded.ok` / `decoded.ok` accesses), so provider
  function is unaffected either way.
- The original raise string (`hir: Unsupported feature: cannot infer
  field type ...`) no longer exists anywhere in `src/compiler/` — the
  HIR field-type inference path was reworked since 2026-08-14. This is
  a material source-state change, not evidence either way: no commit
  identifiable as this row's fix, and no pinning spec exists. Prior
  dispositions re-confirmed, not re-diagnosed: 2026-11-04 P2-w2
  (DEFERRED, needs stage3 canary repro; module_lowering.spl phase-3
  owned) and 2026-11-06 bsB (no fix commit since 2026-10-20; native
  repro needs a stage3 self-build).
- In-lane reproduction is doubly blocked: entry-closure native builds
  are forbidden in p3fix lanes, and no admitted stage2/stage3 compiler
  artifact exists in this Windows worktree.

Grant carried verbatim for the sanctioned stage-chain lane (answer
both questions: does the current frozen stage2/stage3 still raise, and
does the reworked path preserve the declared cross-module return type
without the redundant annotations):

```
# on the admitted compiler host (per bsB 2026-11-06: heavy slot formerly
# held by phase-3 leaf48)
<admitted-stage3-simple> native-build --entry-closure --emit-archive --no-mangle \
    src/app/provider_cli/native_provider_v1.spl -o /tmp/provider_canary
# PASS criterion: no "cannot infer field type ... struct
# 'ProviderQueryWireWriteV1' field 'ok'" (or its reworked equivalent);
# then drop the explicit local annotations in native_provider_v1.spl and
# rebuild as the fail-before/pass-after witness.
```
