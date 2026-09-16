# Bootstrap Rust toolchain sysroot resolution

Owner: Astra bootstrap phase-check lane. Status: Phase 1 published; intermittent metadata failures remain under investigation before Stage 2 admission.

The previous run stopped at `could not resolve canonical Rust toolchain` in
`scripts/bootstrap/bootstrap-from-scratch.sh`. The resolver in
`scripts/check/lib/bootstrap-stage3/authority.shs` invokes the selected Rust
frontend with a clean environment, then passes its native sysroot output directly
to POSIX `cd`. It emits extensionless executable authority paths on Windows.

Focused evidence on 2026-09-08:

- `build/native_probe/astra_toolchain/resolver.before.log` rejects the current
  interactive PATH's literal `%USERPROFILE%` entry. The full bootstrap already
  canonicalizes PATH, so this does not reproduce the historical failure.
- `build/native_probe/astra_toolchain/resolver.normalized.before.log` succeeds on
  the unchanged resolver after matching the bootstrap PATH normalization. The
  frontend returns a native `C:\\...` sysroot; this Git Bash accepts that form.
  Therefore native path handling is a portability weakness, but not yet proven
  to be the sole historical failure on this host.

The repair stays in the existing shell bootstrap authority boundary; Simple
source cannot resolve the Rust seed required to produce its first compiler.
No Rust/runtime implementation change or seed fallback is authorized by this bug.

Required regression: canonical POSIX and native Windows sysroot output (including
CRLF), exact `.exe` identity on Windows, rejection of relative/multiline output,
missing binaries, and policy-channel override attempts. A focused live resolver
receipt must precede any new full-bootstrap attempt. Preserve existing caches.

Unblock condition: focused authority tests pass and a changed bootstrap candidate
advances past Rust authority resolution. Later compiler/deployment failures remain
separate owned blockers; do not call this evidence Stage 4 admission.

Implemented: `bootstrap_stage3_rust_sysroot_path` normalizes Windows drive paths
and trailing CR while rejecting relative/multiline output. Windows authority
receipts now name `rustc.exe` and `cargo.exe` explicitly. Strict channel/PATH and
non-symlink authority checks remain intact.

Verification on 2026-09-08, each command executed once after the repair:

- `sh test/01_unit/scripts/bootstrap_rust_toolchain_resolution_test.shs`: PASS.
  Covers POSIX/native/CRLF output, exact executable identity, policy-channel and
  environment isolation, missing binaries, relative PATH, and malformed output.
- `sh build/native_probe/astra_toolchain/probe-resolver-after.sh`: PASS. Retained
  `build/native_probe/astra_toolchain/receipt.env` binds the resolver authority
  SHA-256 `7dfd420b3e265589256029acf9cf2ea15eb5904987b805ff23c2574781f82153`,
  exact installed stable GNU-host Rust/Cargo `.exe` hashes and successful native
  version launches under a clean environment. Scope: toolchain resolution only.

Safe bounded bootstrap resume from this Windows repository:
`sh scripts/bootstrap/run-phase1-local.shs --output=build/bootstrap`.
The existing wrapper invokes the canonical Windows full-bootstrap path, retains
the cache and stops after Stage 2. The parent bootstrap owner must first confirm
no live writer owns that output. This lane did not run full bootstrap or deploy.

## Resumed investigation, 2026-09-08

The user explicitly resumed diagnosis and requested Astra to fix and continue.
The retained 18:26 failure ends at `fingerprint-step=resolve-rust-toolchain`, but
the fixed inner diagnostic markers were added at 18:33. Absence of those markers
in that older log cannot identify an early resolver guard. It is not proof that
Rust compilation failed: four earlier Cargo logs reached `Finished` before
publication, and the deployed seed still predates that attempt.

The current helper (`df61ac195fb9d66b99196ba74120ebf438e5caddb994bb0b5dd768e3a4ca0697`)
was re-executed through the production provenance facade with the exact PATH
retained in the failed manifest. It passed every installed-toolchain check.
The source-bound observation is
`build/native_probe/astra_toolchain/resumed-current/receipt.env`; result SHA-256
is `91572789161c05d750afae2349db8c94887350caac3bbf2c21b6de5c76a25811`.
The old 16:03 probe used a different helper and is not current admission evidence.
No duplicate resolver definitions or an IFS/command-hash collision were found.

The resolver now emits fixed, opt-in early guard markers for root, PATH,
policy/channel and frontend discovery. Behavioral fault injection proves that
duplicate policy/settings keys and failing installed `rustc`/`cargo` launches
fail closed under nested command substitution, retain the specific marker,
emit no partial authority stdout and never fall back to the PATH proxy. Existing
POSIX/native/CRLF and exact `.exe` tests still pass. The two focused commands
passed once in exec session `15117`; shell syntax passed in the same invocation.
These tests establish diagnostic and authority behavior, not a reproduction of
an unobserved historical Windows process fault.

After a live process inventory confirmed no bootstrap writer, the parent froze
compiler/runtime/bootstrap sources. One strict, cache-preserving canonical
`run-phase1-local.shs --output=build/bootstrap` attempt was started with
`SIMPLE_NO_STUB_FALLBACK=1`. Its exact exec handle is `63519`; logs, prior error
copies, source hashes and run status are retained under
`build/native_probe/astra_toolchain/resumed-full/`. Poll that handle until a
terminal result; a quiet log is not permission to restart it. Deployment,
Stage 4 admission and push remain unproven.

The resumed canonical run terminated with exit 1 after 1714 seconds, having
passed all four Cargo builds and both remaining Rust input checks. It published
generation
`6795aaefe6d6ef7867b26bc41ad9a94fe79ea13e6632b359bb4eca3238cb3658-e56fd55dba690ef561106900c2fa94b899258047690f32d87ce8fd32dd1713b2`.
The current marker and v2 seed stamp bind seed SHA-256
`6d7dee165170d839c569288c7171d81118857e19026db95553a3aad97fde1e52`,
native-all SHA-256
`665161c9c751d14b1f164ba572f038793014be16512ed320cf4dd37188323ad4`,
and backfill SHA-256
`4cdf12fd79d4e7725f353ed3d20a5299ad644f94bf5a34ba14a48eef65c8b94a`.
The authority and driver source hashes remained unchanged for the entire run.

The terminal failure was later: Windows GNU tool-authority binding required an
absent `cc` alias despite the actual build selecting `gcc`. Its deterministic
reproduction and repair are tracked in
`bootstrap_windows_gnu_missing_cc_tool_authority_2026-09-08.md`. No Stage 2
artifact was produced by this run. The earlier intermittent resolver failure
was not reproduced; no native-process crash cause is claimed.

## Metadata failures after Phase 1 publication

The authorized trust-root continuation (`--full-bootstrap --stop-after-stage2`)
does not force a Rust rebuild when the published tuple is current. The first
continuation (exec `11604`, exit 1) failed at the exact installed `cargo.exe -V`
probe. Exact clean-environment and explicit Windows environment-field probes
all passed afterward, so no environment-field fix was justified. The next
changed-code run (exec `59663`, exit 1, 243 seconds) passed both Cargo probes
and stopped after `resolve-native-toolchain`. No Rust build or Stage 2 compile
occurred in either attempt. Retained evidence is under
`build/native_probe/astra_toolchain/stage2-trust-root/` and
`build/native_probe/astra_toolchain/stage2-cargo-capture/`.

The native block has no `ar` query. C version nonzero status is recorded, not
rejected; terminal candidates include C selection/canonicalization and the
LLVM version/prefix queries. Replaying exactly that block with the failed PATH
passed. Its source-bound receipt is `native-block-context/receipt.env` under
the same probe root; records SHA-256 is
`32ecae7e3ffce85959fe917fd5defed970ef62db2ef02f57d20b7ee8e167b1ed`.

A shared metadata-only helper now permits at most two immediate launches of
the same exact executable with identical argv and clean environment. It checks
the executable hash before and after every launch, buffers stdout until success,
retains both attempt statuses and up to 4096 stderr bytes per attempt, and rejects
changed executables. It adds no sleep, PATH fallback, or environment weakening.
This is bounded recovery for read-only metadata queries, not a proven Windows
process root cause or permission to retry builds. Cargo and fingerprint LLVM
version/prefix queries use it. Fixed C/LLVM substep markers identify any remaining
failure; C version-status fingerprint semantics are preserved.

Focused fault tests passed for success, first-fail/second-pass, both-fail,
binary mutation during either successful or failed launch, and rejection of
relative executable lookup. The production native block rejects LLVM faults
with both statuses and bounded diagnostics while preserving C nonzero records;
the Rust resolver regression also passed. A changed-code native replay passed
with exactly the prior records hash (`native-block-recovery/receipt.env`).
These are focused repair checks; Stage 2 admission and compiler/runtime test
coverage remain separate requirements.

The prepared trust-root continuation (exec `55157`) completed its fingerprint,
then reported a different input digest:
`5b9fc718b3f03468c7c77f0e01cac17965e854b380c24495d046390e4e017773`.
The published digest remains
`6795aaefe6d6ef7867b26bc41ad9a94fe79ea13e6632b359bb4eca3238cb3658`.
The supervisor stopped the run on the unexpected Rust rebuild, as required by
the continuation boundary. Exact handle `55157` is terminal (exec exit 1) and
the final process inventory found no remaining owned build processes. The
wrapper's `run.env` recorded status 0 during interruption; it is not admission
evidence. The authoritative stop receipt is
`build/native_probe/astra_toolchain/stage2-native-recovery/abort.env`.

Authority source SHA-256
`6e3c50545840c5dcba35abcbfac171ae0d83ccf9bb22aac6739555c10865caf0`
and driver SHA-256
`fef03bdc15bce2593698be5d6ca46cb501fafc7c58a2a18c86a385e77a4f23cc`
were unchanged throughout that run. The bootstrap message calls the mismatch
"Rust source content changed", but the digest also covers root policy, target
and tool metadata; no changed source file has been established. Successful
fingerprint temporary records are not retained, and the published stamp stores
only the aggregate digest. The changed-input cause therefore remains for the
next scoped diagnostic lane. The published Phase 1 tuple was preserved; the new
fingerprint's partial Cargo cache is retained. No Stage 2 artifact was admitted.

## Modern rustup settings schema (2026-09-09)

Windows installed-rust authority also failed closed at `settings-host=parse-fail`
when rustup metadata omitted the legacy `default_host_tuple` and provided only
`default_toolchain = "stable-x86_64-pc-windows-msvc"`. The authority now
accepts either schema: the modern value is used only when it matches the
selected policy channel, while conflicting dual keys, duplicate keys, missing
channel prefixes, and empty/invalid hosts remain rejected. The focused resolver
test covers legacy, modern x86_64/aarch64 MSVC hosts, conflict, duplicate,
wrong-channel, malformed, missing-key, and invalid-host cases.

The current host path authority is recorded in
`config/host/DESKTOP-VMF96U6.sdn`; it binds only verified canonical POSIX
directories and places `/c/Users/ormas/.cargo/bin` first for rustc/cargo
discovery. The config/schema and sourced-shell lookup oracle must pass before a
new bootstrap attempt; this host fix does not imply bootstrap success.

The host loader now preserves declared PATH precedence while remaining
idempotent; the MSVC chain oracle confirms rustc/cargo resolve from the rustup
proxy and LLVM, VC, MSYS, and SDK directories retain their required order.
