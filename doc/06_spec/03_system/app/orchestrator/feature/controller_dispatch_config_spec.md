# Private local controller dispatch configuration

Status: **NOT_RUN — awaiting verification**. Authored from real filesystem
assertions; not SPipe-generated execution evidence or authenticated-dispatch PASS.

- Spec: `test/03_system/app/orchestrator/feature/controller_dispatch_config_spec.spl`
- Diagnostic: `test/fixtures/orchestration/controller_dispatch_config_native_probe.spl`
- Owner under test: `src/lib/nogc_sync_mut/orchestration/controller_dispatch_config_v1.spl`
- Authored labels: ORCH-02, HOST-02. Intended assertion mappings only; existing
  shorthand requirement reconciliation remains pending.

## Setup and trust limits

Each scenario creates its own secure private parent under `/tmp`, then separate
controller and host root directories. The fixture publishes the exact existing
controller.sdn marker through exclusive creation and fsyncs the marker and root.
The supplied policy contains a synthetic PUBLIC key (32 bytes of0xab), typed
snapshot metadata and positive expiry900. No private key, real signature or
current signed-grant authorization is exercised; these are installation tests.

The fixture uses current shared policy and config encoders. It does not shell
out, mock file operations or replace owner methods. Installation/load call the
actual owner, while independent bounded reads compare the installed bytes.
The caller must own the private root and trusted ancestor tree: mode/path tests
do not establish UID ownership or handle-relative race-proof filesystem access.

## Scenarios

### Install and independently load a durable private context

1. Install canonical config and policy into the new controller root.
2. Check target local-inprocess, exact controller and host-root references,
   host-authority reference, administrator provider-identity pin, policy source SHA-256, session generation3 and the
   synthetic public-key byte171.
3. Independently read dispatch-config.sdn and authority-policy.sdn and compare
   exact supplied bytes. Check root mode0700 and both file modes0600.
4. Require file_fsync for both files and directory_fsync for the root to succeed.
   Load again and compare config pin and loaded policy digest.

This checks actual filesystem calls and source integrity, not power-loss/crash
qualification, host-root attestation or cryptographic authentication.

### Replay exact bytes after a complete policy-only publication

Pre-publish and fsync only the policy, verify config is absent, then call install.
Repeat identical installation and compare policy digest plus both retained files.
This is a controlled completed-policy/missing-config recovery state, not a claim
that arbitrary truncated files or all crash windows can be repaired.

### Reject conflicting config and policy

After valid installation, change epoch and reject immutable config mismatch.
Supply another canonical policy under the old config pin and reject pin mismatch.
Then use a changed config pin consistent with the other policy and reject the
existing immutable config conflict. Independently read both files after every
refusal group; committed bytes must remain exactly unchanged.

### Reject weak modes and policy tampering

Make config0644, then policy0644, then root0755 in separate checks; each load must
refuse the specific private-file/root condition. Restore protected modes between
checks. Replace policy bytes with another canonical policy while retaining the
old config pin; load must fail with local-policy-digest-mismatch.

### Require exact marker, controller identity and independent root paths

Reject another controller ID, relative/root/trailing-slash/dot-parent/empty-path
component/newline root strings, and a host root equal to the controller root.
Reject a relative host path and malformed provider-identity digest. Replace the marker with wrong bytes and refuse a
new install. These are administrator path/marker checks, not native-host proof.

### Refuse real filesystem symlinks without changing their outside targets

Create a linked root and a linked ancestor; both installations must fail as
not-real roots. Unlink only those fixture-owned links. Link the policy leaf to
an outside file and refuse install; read the target independently to prove its
bytes unchanged. After a normal install, link the config leaf to an outside
file and refuse load, again comparing target bytes. Unlink the owned symlink
before recursively removing the fixture-owned private parent.

### Reject malformed, ambiguous and byte-oversized administrative input

Reject incomplete SDN, noncanonical trailing bytes, unknown authenticated=true,
string-valued controllerEpoch, unsupported remote target and duplicate epoch.
Confirm8193 copies of two-byte é are16386 UTF-8 bytes and reject the16KiB config
ceiling. Reject an oversized policy before either installed file exists.

## Assertion mapping and cleanup

| Authored label | Concrete intended checks |
|---|---|
| ORCH-02 | Immutable configuration/policy association, exact replay and complete-policy/missing-config recovery |
| HOST-02 | Private-root/leaf mode, exact marker, path/symlink and pinned-policy integrity refusals |

Successful scenarios remove their own private parent after unlinking any test
symlinks. An assertion failure can leave its private tree for diagnosis; no other
root is removed. No scenario infers enrolled host authority, available capacity,
key publisher trust or signed execution permission from decoded configuration.
Actual consumer/signed/provider checks remain separate. No build, admitted SSpec,
native run, SPipe manual maintenance, coverage or full-system result is claimed.
