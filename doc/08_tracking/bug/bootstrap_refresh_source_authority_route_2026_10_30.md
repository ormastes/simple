# Bootstrap compiler rejects native SSpec authority refresh

The native SSpec runner stages generated test source and invokes the compiler
with `--refresh-source-authority`. The Pure bootstrap compiler rejected that
option before any test assertions ran, even though the canonical native-build
coordinator already implements its authority semantics.

The bootstrap coordinator validated raw worker arguments and could publish a
parse-closure prepass before the canonical coordinator consumed refresh intent.
Route an ordinary explicit refresh request to the existing canonical owner
before those steps. Preserve original argv so that owner clears/reacquires the
source authority and invalidates the old prepublished closure. Do not merely
whitelist or strip the flag, and do not refresh from workers or strict profiles.

Classification reuses the canonical request parser for duplicates and option
values. Worker/shard roles, inherited internal state, Stage3/4, and grouped
refresh requests are rejected. Ordinary requests without refresh retain their
existing dispatch. The canonical coordinator retains argument validation,
memory admission, producer binding, and source authority ownership.

Failure evidence: `/work/native-sspec-calibration-6304-20261030/green-reserve/runner.log`.
Producer SHA256 `6304c166acbcac0a1ea78534fc9a5859507a87ad655eabf98618c798045ad6e8`;
runner SHA256 `44db57b4b3656f310b32d67ed7adb33c4f1894e110405f2f2746db19dd86542e`.
The compiler returned `Error: unknown option: --refresh-source-authority`.
No SSpec assertions ran; this is not a failing user assertion or a test pass.

Focused executable cases live in
`test/01_unit/app/cli/bootstrap_source_authority_refresh_spec.spl`. They check
ordinary refresh, flag-like values, duplicates, internal roles, both strict
profiles, and grouped request refusal. Seed diagnostics are diagnostic only;
a new canonical producer must demonstrate actual native SSpec execution before
this route receives native qualification.

Focused Rust-seed diagnostic: one file, six tests executed, six passed, zero
failed, wrapper exit0 in18.722s. Log
`/private/tmp/astra-bootstrap-refresh-route-seed-final.log`, SHA256
`0cd7c2b72f8cc607e56dc1485c7adb1b1c9735c61459a320d24bd102c3f62939`.
Astra reviewed the final production route and cases with no blockers. The first
five-case diagnostic also passed; the final run adds explicit grouped refusal.
