# Actual-driver native object reuse

Status: AUTHORED, UNRUN. Source freeze and admitted runtime qualification prevent execution in this lane. No PASS or performance target is claimed.

Executable owner: `test/03_system/compiler/incremental/object_reuse_driver_spec.spl`.

Scope: ordinary per-object reuse after full current source parsing, type checking and MIR construction, plus capsule and object receipt checks. These cases do not establish SCV admission, imported body omission, full asynchronous ActionKey publication, or the warm-entry latency target. Root must separately run the managed SCV source-generation fixture through the genuine lane02 typed epoch scope.

The reference build has distinct frontend-reference, hir-reference and native-reference directories. Ambient compatibility imports and shared parse CAS are disabled. Missing candidate authority fails setup; unsupported source constructs fail visibly rather than accepting fabricated output.

Authored scenarios:

1. changes the entry and reuses its authenticated current-input provider object bytes.
2. invalidates a provider body without linking stale bytes.
3. invalidates a public return signature.
4. invalidates an instantiated generic body.
5. invalidates a consumed default expression.
6. invalidates a published constant.
7. invalidates a module initializer.
8. rebuilds a missing or corrupted dependency object and receipt.
9. invalidates an optimization configuration without erasing the old scope.
10. refuses changed invalid source before stale native publication.
11. invalidates a referenced external record layout.
12. invalidates a target-selected static guard.
13. invalidates a recorded negative import query when the preferred module appears.
14. invalidates a visible overload candidate set.
15. invalidates a selected trait implementation body.
16. invalidates an active aspect body before native publication.

17. Ordinary prepared-import entry action publishes an actual ELF ET_REL object before final link, keeps imported bytes/receipt unchanged, and refuses a missing imported ObjectReady before new imported emission. This is authored and unrun, scoped to the actual Linux host; no warm-header or latency PASS is claimed.
