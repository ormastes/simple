# Actual Windows fixed machine storage ownership V1

Status: **AUTHORED_NOT_RUN**. Manually authored companion to
`test/03_system/tools/windows_machine_storage_v1_spec.spl`; no runtime, test,
docgen, native build, or Windows fixture was executed. This is source review
material, not verification PASS or release admission. Existing native journal
exports and the canonical global-root extension still require owner admission.

Use a disposable, independently administrator-prepared actual Windows image.
The fixed ProgramData installation must contain the protected nonempty UTF8
`Simple\Container\machine-policy.sdn` and existing protected `state` directory.
The real journal factory must be able to acquire its fixed writer. The test
does not install a fixture, modify ACLs, fabricate owners, accept root inputs,
or skip an unsupported host. Binding can publish the fixed
`machine-capacity-policy.sdn`, so this scenario is unsuitable for live state.

1. **Transfer the actual installed reader into fixed state and journal
   ownership.** Open the fixed production factory, then transfer its actual
   owner. Read actual bytes through storage. The reader alias must refuse
   further reads and transfers, and its close must report `retained` while
   storage owns cleanup. No raw root, journal, path, or HANDLE is exposed.
2. **Reject a competing actual writer without abandoning its cleanup owner.**
   Open another real reader and request storage while the first writer lives.
   Require refusal and confirmed `released` cleanup of its actual result.
   Unexpected Ready also receives cleanup and fails the scenario. Every reader
   and storage result remains in diagnostic owner arrays, including retained
   partial opens.
3. **Bind only exact installed bytes and reject invalid transactions before
   publication.** Attempt differing bytes, then bind the exact observed UTF8
   policy and compare its digest. Observe the actual WAL head; reject an empty
   transaction and a transaction for a table outside the fixed allowlist.
   The same actual head must remain readable and unchanged. This creates no
   reservation fixture rows and does not erase preexisting charges.
4. **Close the canonical storage before asserting collected results.** Require
   `released`; copied storage reads and head queries must fail, and copied
   storage and reader repeated closes must return `stale`. Cleanup follows the
   production journal, private-root, retained-reader order; failure to release
   remains retained authority. No compensation, ledger reset, or release
   record is synthesized.
5. **Reopen the same fixed state without resetting durable policy or WAL.**
   Reacquire the writer, bind the same actual policy, compare the binding digest
   and actual WAL head with the first opening, and confirm cleanup again.

The executable scenario exercises the existing owner ports directly, including
the shared `Some(journal)` WAL route. It does not establish authorization,
reservation admission, charged accounting, enrollment/deployment adoption,
delegation, native cleanup failure behavior, or power-loss durability. Those
need separate producer-bound evidence. No coverage percentage is claimed.

The drive-root ProgramData regression remains **MANUAL_NOT_RUN**: use a separate
administrator-prepared disposable image whose actual OS ProgramData is a local
drive root, with the same protected fixed installation. The reader already
admits that OS path; transfer must address
`\GLOBAL??\<drive>:\Simple\Container\state` with one separator, and must never
fall back through a normal DOS pathname. On an ordinary non-root ProgramData
image, the separator between ProgramData and `Simple` must remain present.
No helper accepts an injected path to simulate either case. Unicode ancestry,
local DOS shadowing, cross-thread calls, partial cleanup failures, and uncertain
publication quarantine remain separate isolated native obligations.

Traceability: the alias and repeated-close assertions extend
REQ-WINDOWS-MACHINE-POLICY-003; repeated actual bytes and exact binding extend
REQ-WINDOWS-MACHINE-POLICY-002. Writer exclusion, fixed WAL routing, and durable
reopen observations are authored storage-boundary checks, not a claim that the
unfinished shared physical-capacity authority is complete.
