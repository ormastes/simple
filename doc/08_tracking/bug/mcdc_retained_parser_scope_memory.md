# MC/DC native builds retain parser scratch

Status: source fix applied; native and full-build verification pending.

The 2026-10-15 pure-Simple full CLI qualification exceeded its enforced
8,388,608 KiB tree RSS cap during parsing, at 816 of 2,673 source files.
Observed peak was 8,390,944 KiB, exit status 88. No objects or linked CLI
were produced; the supervisor confirmed quiescence and no session escapes.

`parse_full_frontend_selected_v1` bypassed the existing per-source transient
scope whenever coverage, MC/DC, or full-inventory selection was active.
The failed qualification required MC/DC, so it followed that unscoped route.
This establishes an ownership defect, although the observed peak does not
separate retained AST bodies from parser and serialization scratch.

The fix uses the existing scope for every AOT selection, retains cumulative
coverage manifests and collision maps, promotes the actual target receipt
dictionary, and replaces per-source coverage and placeholder scratch after
scope teardown. It preserves MC/DC and complete source membership. Promotion
currently traverses accumulated inventory per source; its cost remains to be
measured.

Native regression: `test/02_integration/compiler/coverage_retained_parse_owner_probe.spl`,
executed separately with `--coverage`, `--mcdc`, and `--full-inventory`.
It checks actual scratch reclamation, retained/desugared bodies, accumulated
coverage and obligations, existing replay semantics, target receipts, and
parser diagnostic survival/recovery. Interpreted execution cannot qualify
native allocation lifetimes. All three executions are currently UNRUN.

Acceptance also requires the bounded full object build, exact object/link
membership, and executable Hello World. A bootstrap producer's objects are
not Phase 3 qualification evidence. Per-object recovery must retain source
SCCs and admitted dependency artifacts rather than silently dropping sources.
