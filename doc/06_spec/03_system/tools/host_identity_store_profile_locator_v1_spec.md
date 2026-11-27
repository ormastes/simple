# Actual exact-profile retained configuration locator V1

Status: **AUTHORED_NOT_RUN**, manually mirrored from
`test/03_system/tools/host_identity_store_profile_locator_v1_spec.spl`. No test,
build, native call, key generation, SSH launch, docgen or deployment occurred.

Prepare disposable actual OS fixtures independently. Linux uses a trusted
current-user root/journal with0700 directories and0600 regular profile files,
and runs on the genuine canonical main thread. Windows uses a protected native
GLOBAL?? root; no ordinary-drive fallback or synthetic namespace owner is used.
The fixture must contain a genuine complete canonical ServerSshProfileV1 whose
filename stem equals the SHA256 of its actual canonical UTF8 bytes. Its storeRoot
field equals the fixture root. Actual key/known-hosts references and full profile
fields are independently provisioned; the test publishes nothing.

| Environment | Preparation |
|---|---|
| SIMPLE_HOST_IDENTITY_PROFILE_LOCATOR_ROOT | Actual protected profile store root; Windows explicit GLOBAL?? spelling. |
| SIMPLE_HOST_IDENTITY_PROFILE_LOCATOR_LEAF | Existing exact64lowerhex.profile full canonical record, not key/hosts data. Leave the all-zero-stem .profile genuinely absent. |
| SIMPLE_HOST_IDENTITY_PROFILE_UNSAFE_ROOT | Separate protected root/journal containing the64-b-stem .profile as actual symlink/reparse or unsafe-mode/type target; do not alter live files. |

1. **Validate the actual profile target.** Open the production store and capture
   actual bounded profile bytes only inside memory. Strictly decode them and
   compare the public filename stem with their actual SHA256. Call the new
   locator and unchanged generic path/preflight functions.
2. **Exercise production role refusal.** Query .key/.hosts, uppercase/nonhex or
   short/long stems, alternate suffixes, traversal, child and NUL spellings;
   require the exact profile-role refusal. No owner is fabricated to reach the
   grammar branch, and no private key path is returned.
3. **Forward original namespace data to the actual loader.** Close the initial
   writer before the loader reacquires the same protected root. Pass the exact
   returned locator to server_ssh_profile_load_v1 without transport normalization.
   Retain and attempt cleanup of any actual returned cleanup owner before
   assertions. Require successful strict load and compare every full public
   field with the original actual protected decode, including storeRoot.
4. **Preserve generic behavior.** Windows locator retains GLOBAL??, while
   unchanged generic path/preflight still return transport-projection-unavailable.
   Linux returns the original retained spelling and generic behavior succeeds.
   A copied closed owner cannot produce another locator.
5. **Distinguish actual absence from failure.** The separately absent valid role
   yields profile-absent, then the existing profile still locates. A real unsafe
   target yields an actual failure rather than absence/role refusal, leaves
   canonical cleanup pending, and never returns locator data. Cleanup precedes
   assertions and every partial native owner stays in the diagnostic list.

The following remain **MANUAL_NOT_RUN** and require real isolated faults:
target replacement/drift, reparse/permissions/owner mismatch, partial read or
failed close, Linux fork/PID-namespace/worker-thread refusal, retained Windows
cleanup, oversized or malformed profile data, and concurrent writer admission.
Failed loader cleanup must remain owner-bearing; do not fabricate success or
retry a consumed descriptor. A path string after close is data only, and fresh
loader validation is mandatory. Actual SSH and Service interoperability,
namespace projection and OpenSSH token expansion are separate consumer proofs.
