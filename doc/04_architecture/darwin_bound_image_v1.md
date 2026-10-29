# Authenticated Darwin image owner V1

The native image owner now derives launch identity from a caller-authenticated
artifact digest without a pathname verification race. This is executable-image
enforcement with the existing cooperative process-group lifecycle. It does not
admit a strict BuildRunner tree or promote V4 capabilities.

## Identity transformation

1. The caller supplies a trusted SHA256 for the original artifact. It must come
   from the caller's authenticated manifest/request, not from a fresh hash of
   an attacker-controlled path immediately before calling this API.
2. The owner reads at most 256 MiB from an opened regular-file descriptor into
   private memory and checks that digest before interpreting executable identity.
3. A bounded parser accepts a thin, native, dynamically linked Mach-O executable
   using `/usr/lib/dyld`, an `LC_MAIN` entry within `__TEXT`, and one terminal
   code-signature region. Fat binaries, scripts, encrypted images, non-native
   subtypes, legacy thread entry, and embedded dyld environment commands reject.
4. The owner copies the authenticated prefix, updates only code-signature and
   `__LINKEDIT` sizing metadata, and creates a fresh ad-hoc CodeDirectory with
   hard, kill, and hardened-runtime flags. All prior signing metadata and
   entitlements are removed. Pages and the signed library policy are hashed
   from this same in-memory representation; no external signing process or
   pathname-based Security-framework inspection participates in derivation.
5. The library constraint admits no custom CDHash (a zero CDHash requirement).
   Apple exempts OS libraries from this policy. The OS and system libraries are
   trusted; arbitrary custom libraries, JIT exceptions, scripts/interpreters,
   and preserved developer entitlements are outside this profile.
6. The generated signature's CDHash is attached to `posix_spawn` using AMFI.
   Policy bytes belong to the image; caller attributes must be destroyed before
   closing it. The bound path checks the fixed provisioned size and inode, but
   never rehashes a mutable file to EOF. Replacing or mutating the mutable
   on-disk copy can cause denial; it cannot admit a different CodeDirectory.

The `source_digest` and derived `cdhash` are retained in the image owner. The
filesystem object is not immutable. The guarantee is a kernel-bound image,
with denial/SIGKILL allowed after hostile modification.

## Native interfaces

- `sosix_darwin_image_create_bound` implements authenticated provisioning.
- `rt_sosix_darwin_bound_image_v1_start_value` accepts canonical lowercase SHA256
  text, the existing invocation/environment/limits vectors, and returns
  `[version,error,handle]`. It uses the production runtime object and existing
  snapshot poll/cancel/output/ack registry. The old snapshot entry point still
  accepts only explicit profile 1 and retains its original cooperative image
  contract; it never upgrades or falls back implicitly.
- `darwin_bound_image_start` is the thin Simple FFI facade. It does not turn an
  interpreter into a native provider or claim deployed P2 qualification.
- The native runner adds explicit `--profile bound-image-group --sha256 DIGEST`.
  Its separate capability query reports AMFI SPI availability, not strict
  provider qualification. Existing snapshot CLI output remains compatible.

All descendants must still remain in the created process group for lifecycle
cleanup. Image binding does not forbid later exec, credential elevation, IPC
delegation, or process-group escape. Those require separate tree authority and
policy. User-controlled data files and the caller's manifest transport are also
outside the executable identity primitive.

## Host and implementation limits

Direct AMFI attachment and LWCR DER are private Apple interfaces. The owner
requires the third-party-constraint sysctl and attachment symbol, failing before
source acquisition when unavailable. The native suite compares its narrow DER
encoding with Apple's serializer and tests real kernel enforcement on the local
Darwin arm64 host. Other OS builds/architectures are not qualified by that result.
Ad-hoc provisioning changes signing identity and intentionally drops entitlements;
it is not appropriate for arbitrary platform-signed applications or bundles.

## Evidence

The TDD initial provisioner returned `ENOTSUP` and failed the native acceptance
assertion. Authenticated malformed-command/signature/loader fixtures exercise
the parser with fresh matching digests. The implemented provisioner then passed AMFI launch and Apple's
`codesign --verify --strict`. The owner suite deterministically replaces and
mutates the image after the final userspace check. Replacement cannot reach
constructor or main-entry markers. Mutation may allow earlier authenticated
pages to execute before a later page fault; it must terminate without a
successful result. An attacker growing the file to a 1 TiB sparse extent is
rejected without a moving-EOF hash scan,
and tests custom-library denial with a working unconstrained injection control.
The runtime-object suite verifies the new entry point alongside existing
capture, timeout, cancellation, fork, stale-handle, and preflight behavior. The
worker test executes the correct digest and rejects an incorrect one before
execution. These checks build small native C fixtures only; no P2 rebuild.

UBSan passed the parser matrix and native signature launch. The local ASan
runtime deadlocked during its own initialization before `main`; it was sampled
and terminated, so address-sanitizer coverage is not claimed. See
`doc/08_tracking/bug/darwin_asan_initialization_reentry_2026_10_29.md`.
