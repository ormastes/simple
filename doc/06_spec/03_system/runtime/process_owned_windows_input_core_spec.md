# Windows immutable stdin core scenario manual

Authored manual; native SSpec/docgen execution remains pending. Source:
`test/03_system/runtime/process_owned_windows_async_spec.spl`.

Audience: runtime maintainers admitting Windows process execution. Build the
native C fixture with `scripts/check/check-owned-process-windows-async.ps1`,
then run the SSpec with an admitted Windows-native Simple producer.
A missing producer or fixture fails with `MissingEvidence`.

| Requirement | Operator steps | Required outcome |
| --- | --- | --- |
| REQ-WIN-INPUT-001 | Start a binary echo child with input larger than the pipe buffer; mutate the caller's bytes; poll and collect; repeat with empty input and invalid/stale authority. | Child bytes and SHA-256 match the accepted snapshot. Written/accepted counts are exact, stdin reaches EOF, and invalid authority grants no input access. |
| REQ-WIN-INPUT-002 | Start a non-reader with the maximum input; zero-wait poll; complete an independent lease; cancel and collect. | Poll stays bounded, independent progress continues, pending I/O completes before terminal/collection, and written input is less than accepted input. |

The native fixture asserts byte content and receipt fields before emitting its
suite marker. SSpec requires exit 0, empty stderr and the corresponding marker.
Portable Win32 API fakes separately test completion/cancellation state changes;
they do not qualify Windows behavior. Opaque V3 facade, sealed pins and V4
remain unsupported. No Windows-native PASS has been recorded on macOS.
