# Configured Windows primary geometry through the authenticated common service

Source: `test/03_system/app/orchestrator/feature/windows_primary_geometry_native_v2_spec.spl`.
Fixture: `test/fixtures/orchestration/windows_primary_geometry_service_v2.spl`.
Status: one genuine configured-service scenario AUTHORED_NOT_RUN. No admitted native campaign was started. This manual is authored from source, not generated test evidence.

## Required real setup

An administrator must run the actual enrolled generic V5 service with its retained protected Host domain, real Docker Engine API 1.48 endpoint, and a dedicated genuinely created running Windows TTY container. Complete actual signed parent/helper admission, native attach and sole-pane adoption before starting the test. The service must retain its current protected credential and actual attachment lease. Neither a copied plan nor test metadata can fabricate that live owner.

Provision `C:\SimpleQualification\primary-geometry-v2.sdn` as a bounded canonical SDN object with version 1, kind `windows-primary-geometry-service-fixture`, and these fields: `endpoint`, `serverToken`, `bindingUid`, `clientId`, `attachmentToken`, `targetDigest`, `geometryRevision`, `inputRevision`, `inputProbe`. Use actual current values; do not put credentials in logs or evidence captures. The fixture reads a regular no-follow file and fails when the file, Windows native thread guard, authentication, adopted TTY, or current revision is absent.

The binding must be dedicated and fresh for this single run: no previous Input write/frame and no previous Geometry resize attempt in its current leases. `inputProbe` is a deliberately harmless nonempty UTF-8 payload accepted by the dedicated guest fixture, at most 4096 bytes. It is actually written to the attach stream. Reusing a consumed fixture without creating fresh legitimate state is a setup failure. Configure sufficient independent lease lifetimes for bounded test progress; do not bypass expiry checks.

## Executable scenario

1. Issue actual Input authority for the exact expected adopted target.
2. Resolve 100 columns by 30 rows and require the current target digest; issue separate Geometry authority.
3. Submit one canonical resize. Poll at most 256 observations with a 30-second monotonic bound. Require actual HTTP acknowledgement, matching dimensions/sequence/revision/wire digest and completed native cleanup.
4. Repeat the identical request only for evidence. Require identical canonical receipt and publication identity. Change columns under the same attempt and require refusal.
5. Revoke Geometry. Use the original still-valid Input lease for the configured payload; observe a completed native write with the exact accepted byte count, then revoke Input.

There is no automatic mutation resend on transport timeout. A timeout, Unknown result, unavailable prerequisite, partial Input completion or expired lease fails the scenario. It never becomes an unsupported-platform pass. The test does not stop the external service or workload; the qualification harness owns teardown, must cancel pending Geometry, retain unresolved service owners/evidence on failure, and perform normal exact cleanup before removing its dedicated deployment.

## What remains unqualified

This scenario asserts actual common-service acknowledgement and Input independence, **not independently observed guest terminal size**. Guest output/size observation and fault cases remain NOT_COVERED: non-TTY/wrong native ID, Engine/endpoint change, expiry between native install/write, policy revoke during pending IO, partial/unknown write, malformed/lost HTTP response, cleanup failure, process loss after attempt publication, retry after restart with missing receipt, and an internal two-live-connection substitution fault after the original helper/parent retires. The latter requires a native Host fixture retaining two genuine opaque tasks on the same writer; assert that substituting the second task only cleans the first geometry exchange and never performs its write. The wire fixture cannot inject opaque Host tasks, so the pure production-predicate regression is not claimed as that native fault. Production reducer and record specs cover some refusal contracts but do not execute those native faults.

All native behavior, ABI/linking, allocation bounds, whole-service latency/RSS and Windows journal durability remain AWAITING_VERIFICATION. No test result or coverage percentage is claimed.
