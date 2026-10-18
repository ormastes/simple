# Writer-held Windows entry publication: review proposal, not implemented

2026-10-18. Scope: standard-user file authority only. No collector, producer, cache, receipt, or source identity changed. This proposal is not evidence that Windows publication works.

## Existing owners and defect

`src/runtime/runtime_cache_host_authority_v1.c` already creates writable secure TEMP handles, flushes them, sets read-only, renames with handle-based no-replace, flushes the same writer again, then closes it. Reuse that implementation. Its READ handles intentionally cannot flush. `src/lib/common/cache_host_authority_v1.spl` is the existing ABI facade.

`driver_aot_native_output.spl` receipt barrier flushes READ receipt, READ source, then ROOT. Its destination verification later flushes a newly opened READ. Partial Windows provider alone cannot satisfy these calls. Actual producer3c6 additionally contains the older unsupported root-open provider. Neither condition permits fake success.

Production codegen currently returns the final capsule.object_path and writes its original receipt afterward (single owner around3500-3570; grouped owner3272; phase reuse674-718). These paths do not retain writer capabilities. A C-only replacement cannot reconstruct the required preseal authority.

## Smallest candidate public contract

Add one C ABI, tentatively `rt_cache_host_publish_retained_noreplace_v2(temp, relative)`: positive opaque SEALED token on success, zero destination exists, negative failure. Reuse the existing temp writer, seal/rename/flush implementation. Success consumes TEMP and retains its ORIGINAL writable OS handle behind a new sealed, read-only-in-language capability. Reject writes for this capability. Existing publish-v1 remains unchanged and closes its writer. Existing bounded read, size, real fsync, close implementation can dispatch SEALED explicitly; READ fsync remains unsupported. Never reopen an immutable path writable.

Add `CacheHostSealedObjectV2` and typed wrappers in the existing SPL facade; close is mandatory and copied aliases become invalid after the first consuming close. No serialized integer, path, receipt digest, or ordinary READ becomes a durability witness. Root binding, final relative path, retained file identity, sealed state and flush result are native-owned facts.

A pair owner in driver_aot_native_output must create canonical object and original receipt through existing secure-temp/write APIs, publishing each once with retained-v2. Its result transports both sealed capabilities plus roots to the publication owner. Existing receipt bytes and format stay exact. The barrier reads and flushes those SAME sealed handles; it must not reopen READ handles while a writer remains, because sharing compatibility can reject that reopen. Destination copy uses another retained-v2 handle, verifies and flushes that handle, then closes in a single owner cleanup path.

External backend output must be uncommitted staging output first. The driver copies bounded validated bytes from a pinned staging READ into authority TEMP before canonical publication; backend return-path validation must name staging explicitly rather than silently substituting capsule.object_path. Existing phase-reuse staging offers a pattern, not a substitute authority. This changes fresh, grouped and reuse producer boundaries and their result transport; it is therefore not a one-function C fix. Existing immutable cache pairs lacking a live witness remain fail-closed for this route. No receipt rewrite or automatic replacement is allowed.

## Unresolved namespace durability gate

Writer-held FlushFileBuffers proves file flush only. It does not prove directory-entry durability. Source/destination ROOT flush requirements remain actual FlushFileBuffers results; a standard-user denied or unsupported ROOT flush must fail. Before implementing broad producer changes, a focused native test must demonstrate the exact required directory publication contract under an ordinary token on supported Windows, or the public durability specification must explicitly select and justify a different guarantee. No documented handle-based write-through rename substitute has been established here. Admin volume flush is excluded. Thus this proposal fixes the READ authority design but is NOT yet a complete proven Windows durability solution.

## Focused native C ABI acceptance design

One actual standard-user full sequence: pinned root; object TEMP/write; retained seal/no-replace; original receipt TEMP/write; retained seal/no-replace; exact receipt comparison and hash/size through bounded sealed reads; real file flushes and real ROOT barrier; destination TEMP bounded copy; retained publish; same-handle verification/flush and ROOT barrier. Record token elevation, actual Win32 error codes, file IDs, receipt before/after SHA, and original bytes. No successful result unless every specified barrier succeeds.

Negative controls: ordinary READ fsync still fails; consumed TEMP/stale/closed/forged/wrong-kind tokens fail; write-after-seal fails; copied close aliases invalidate; wrong root/relative identity fails; destination exists is zero without replacement; no source receipt mutation; Unicode/long paths; reparse/path swap denial; invalid/empty handles; flush/rename failures; bounded read and copy limits; cleanup after each partial pair. Test real production C ABI and MSVC compile, not mirrored helper logic. Namespace test must run first and stop broad implementation if unavailable. At most three fix cycles; no producer rebuild now.

## Review boundary

Root review required before implementation. Proposed touched source owners: runtime_cache_host_authority_v1.c; common/cache_host_authority_v1.spl; driver_aot_native_output.spl and narrowly required native result/batch ownership types. Existing runtime source identity owner already covers the C file; any new ABI/source cohort must be honestly rebuilt and pinned later. No daemon/GC support claim. Existing diagnostic objects are preserved and remain unpublished.

## Focused ordinary-token observation (2026-10-18, one execution)

The genuine production3666 C ABI was exercised under the canonical enforced1GiB guard after fresh62GiB joint physical/commit admission. TokenElevation=0. Root fsync before publication=1/error0; secure TEMP write and actual no-replace publication=1/error0; root fsync afterward=1/error0. Same pinned root FileID0006000000b97aaa before/after; published file retained TEMP FileID0006000000b97aad and read-only attributes33. Public READ fsync remained-1. A diagnostic direct FlushFileBuffers on the same retained ROOT also returned1/error0. Guard complete/exit0/quiescent1/enforced1/helperverified, peak2640KiB. No product changes or producer rebuild. This demonstrates the root barrier operation is available to this ordinary token/filesystem; it does not prove crash or power-loss persistence or every supported filesystem. The prior namespace gate therefore has positive host evidence, pending root review of the intended durability contract.

Evidence: C:/dev/p3-root-flush-probe/receipt.json SHAaff7926cc15537734e113a47b186fdb1f556dd7d5b1aab1bedbd0a92d75d7739, which pins exact source/executable/provider/tool/stdout/admission/guard inputs. Native execution count1. Initial observer preflight refused before a job due inherited40 requested jobs plus44 other jobs; the corrected observer explicitly requested1 and passed a fresh62GiB admission. No unchanged native rerun occurred.

## Additive implementation checkpoint

Only the retained-sealed C primitive and typed/exported SPL facade are now implemented. Driver fresh/grouped/reuse ownership edits remain unapproved and absent. Focused native ABI59 checks and standalone MSVC /MT production compile passed; SPL native integration is UNRUN. See doc/08_tracking/bug/windows_cache_retained_seal_authority_2026_10_18.md for the pinned evidence and failure semantics. This is not a completed public entry-object fix.
