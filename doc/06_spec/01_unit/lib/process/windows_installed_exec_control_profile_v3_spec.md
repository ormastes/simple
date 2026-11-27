# Installed Windows exec control profile V3 codec

Status: **AUTHORED NOT_RUN**. Pure codec assertions only. This source does not
observe an installed policy, binary, host, Engine or permission grant.

The installed-only profile combines WindowsDockerPolicyV1 and
WindowsContainerStreamPolicyV3 without changing V2. The six exact required
wrapper keys are kind, version, dockerPolicy, dockerPolicyDigest, streamPolicy
and streamPolicyDigest. Kind is `windows-installed-exec-control-profile-v3` and
version is integer3. Component values are their existing canonical SDN texts:
Docker includes its LF and stream does not gain an LF. Each digest is raw64
SHA256 of that exact component. The canonical wrapper has one trailing LF.

The installed observation owner may bind SHA256 of the actual installed wrapper
bytes to observation.installed_policy_digest. The codec's digest function only
derives that value; it neither observes installation nor supplies authorization.
A caller-supplied installedPolicyDigest wrapper field is unknown and rejected.

| Requirement | Authored pure scenario | Expected result |
|---|---|---|
| REQ-WIC-001 | Exact roundtrip and derived wrapper hash | Component bytes/order preserved; digest is SHA256(wrapper), changes with policy |
| REQ-WIC-002 | Wrapper shape and hash binding | Distinct component hash swap, caller observation hash, unknown/missing/duplicate/type errors and noncanonical source refused |
| REQ-WIC-003 | Strict embedded stream policy | Fixed constants, exact two-text env pairs, case-folded duplicate names, unknown/duplicate/type/alias forms refused even with recomputed hash |
| REQ-WIC-004 | UTF8 byte budgets | Wrapper1MiB, embedded stream512KiB and existing Docker16KiB bound checked by byte_len and strict parser source limit |

Nested stream fields exactly match the existing encoder: kind, root,
brokerProgram, brokerDigest, environment, directory, apiVersion, timeoutMs,
headerLimit, controlLimit, frameLimit and pendingLimit. All are required. Limits
must equal the common V3 constants; environment is an ordered array of two-text
name/value pairs. Existing policy encoding validates paths, digests, API version,
time, environment names, folded duplicates and size. Both nested stream and outer
wrapper must exactly match canonical re-encoding. Docker decoding delegates to
the existing strict canonical policy codec.

No compiler, test or Windows runtime was run. No live observation, installed
file read, native trust check or execution capability is claimed. Integration
must get trusted installed bytes through its owner and independently bind actual
host/Engine/control observations; an arbitrary policy hash is never a substitute.
