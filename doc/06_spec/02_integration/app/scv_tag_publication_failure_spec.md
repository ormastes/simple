# SCV annotated-tag publication failures

Source: `test/02_integration/app/scv_tag_publication_failure_spec.spl`.
Requirement: `REQ-SCVN-B03-PUBLISH`.
Status: authored manual; native execution, docgen and maintenance scan
**not_run**. This is a source-review candidate, not passing runtime evidence.

The fixture makes two real snapshots and retains their distinct commit IDs.

| Scenario | Real fault | Independent negative oracle |
|---|---|---|
| Imported annotated-tag object fails | Block the predicted candidate tag object's `.sdn.tmp` staging path with a directory. | Exact object-publication error; both prior tag-reference files unchanged; no error text in metadata; candidate object absent. |
| Lightweight tag reference fails | Block `meta/tags.tmp`. | Error outcome and prior reference bytes unchanged. |
| Annotated tag reference fails | Block the reference staging path, then also submit error text as an object ID. | Staging failure and invalid-object errors; old ID retained; no error text in metadata. |
| Bookmark reference fails | Block `bookmarks.sdn.tmp`. | Error outcome; prior bookmark and head bytes unchanged. |

The object-path digest predicts where to inject the fault; it is not the
success oracle. Assertions read persisted reference bytes after the operation.
Atomicity across both tag references remains a separate pending contract.
