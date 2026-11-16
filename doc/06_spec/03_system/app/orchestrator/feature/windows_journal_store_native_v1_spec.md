# Native retained Windows journal storage

Status: **AUTHORED_NOT_RUN**. This manual is authored from the executable SSpec;
it is not generated or executed evidence. No native build, test, runtime smoke,
fault injection, or docgen was run in this source session.

Source: `test/03_system/app/orchestrator/feature/windows_journal_store_native_v1_spec.spl`.
Evidence class: actual Windows native host fixture. Traceability:
REQ-WIN-PRIVATE-002, REQ-WIN-PRIVATE-003, REQ-WDS-006.

The fixture must run under an admitted self-hosted Simple Windows binary linked
to the changed native runtime. Configure these independently installed roots:

| Variable | Required actual fixture |
|---|---|
| `SIMPLE_WINDOWS_JOURNAL_PRIVATE_PARENT` | Existing absolute fixed-drive directory with a protected, current-user-owned private ACL and trusted non-reparse ancestry. The running principal needs child creation. Each scenario creates its own random private child through the actual Windows root owner. |
| `SIMPLE_WINDOWS_JOURNAL_DENIED_ROOT` | Separate existing protected root with private `journal` child and a real existing `journal/denied.sdn` whose ACL denies the test principal file read access. Leave `journal/fixture-must-be-absent.sdn` absent and permit journal/lock admission. |

Native admission checks the actual handles, ACLs and retained ancestry. Setting
an environment string does not grant authority. Non-Windows hosts, absent
variables, insecure roots, missing denied files and unavailable native providers
are failures; the spec contains no unsupported-host success or skip path.
Run these exclusive-root fixtures serially. Successful scenarios close every
native owner. Published fixture records remain in their random child directories
for inspection; remove them only after test owners and runners have exited.

The principal scenarios are:

1. Admit a real first owner, refuse a second acquisition of its `parent.lock`,
   collect the actual refused owner, then reacquire after release. A copied
   stale generation reports `stale` and cannot mutate or close the replacement.
2. Publish and read exact UTF-8 through journal, WAL and archive descendants.
   Collisions preserve original bytes; actual empty content differs from
   absence. Only `parent.lease` uses unrestricted atomic replacement.
3. Compare and replace `database-wal/CURRENT` through copied owners. Stale
   expectations preserve the latest bytes; `None` and `Some("")` differ. The
   journal remains live after its independent parent root owner closes.
4. Refuse traversal, ADS, absolute paths, internal lock/stage names, excess
   depth and long components, then publish a valid record through the same
   still-live owner.
5. Publish/read eight MiB and refuse larger content before publication.
   Invalid read quotas preserve the owner and cannot fabricate an empty value.
6. Observe exact absence separately from a real denied entry. Denial returns
   an error, closes ordinary authority and retains native cleanup until close.
   The public read error does not expose a specific underlying Win32 code.
7. Mint an opaque consumption receipt only by newly publishing the fixed
   64-lowercase-hex record. Actual readback precedes successful claim; copied
   replay and wrong-payload retries fail. Ordinary publication/read cannot mint
   a receipt, and close invalidates unclaimed receipts.
8. Open two independent protected roots/stores and publish identical consumption
   bytes. Assert exact origin-root and issuing-store correlation, reject the
   other authentic owner, and reject stale correlation after close.

<details>
<summary>Limits and outstanding native qualification</summary>

All eight scenarios remain unexecuted. The lock test uses two real native
owners in one process; cross-process exclusion and scheduling stress remain
unqualified. CAS assertions demonstrate the public stale-expectation contract;
concurrent-thread stress has not run. Receipt capacity exhaustion and malformed
on-disk UTF-8 need additional native coverage. Real failed `CloseHandle`,
`LocalFree`, post-rename verification and uncertain rename cleanup need a
supported native fault-injection fixture; this spec does not pretend to inject
those failures. No power-loss/directory-flush durability claim follows from
authored file-flush and handle-relative atomic rename scenarios.

The independently prepared denied fixture is required. The public error proves
failure differs from exact absence; it does not independently attest every ACL
installer operation. Native fixture preparation and run receipts remain missing
until an authorized Windows qualification run records them.

</details>
