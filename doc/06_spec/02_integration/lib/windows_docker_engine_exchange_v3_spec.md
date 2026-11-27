# Windows actual Engine exchange fixture v3

Status: **SOURCE-ONLY NOT_RUN**. No compilation, test/native execution or Docker
request occurred. This is an authored qualification procedure, not a PASS.

Spec: `test/02_integration/lib/windows_docker_engine_exchange_v3_spec.spl`.
Fixture: `test/fixtures/orchestration/windows_docker_engine_exchange_fixture_v3.spl`.
Source: `src/lib/nogc_async_mut/container/providers/windows/docker_engine_exchange_v3.spl`.

Requires native Windows AOT, an installed running Windows Docker Engine exposing
the fixed local named pipe, API1.48 support, and the native pipe owner's admitted
SYSTEM/Administrators protected DACL profile. Unsupported hosts, interpreter mode,
missing Engine or failed admission fail explicitly; there is no scripted fallback.

The fixture uses actual native pipe connect/read/write/cancel/collect. Its only
HTTP effect is read-only GET /v1.48/info; it creates/starts no workload and makes
no Host signature, execution grant or durable birth claim. Before any write,
begin captures actual server PID/owner/DACL observation from the exact connected
lease. A completed Connection:close response uses this retained actual admission
observation, since a fresh server query after response completion may disconnect.
The getter refuses failed/closing/closed/transferred or unavailable owners.

| Source case | Actual path and intended assertion |
| --- | --- |
| Info | Fixed pipe request returns complete actual200 JSON, Windows OSType plus nonempty engineID/kernel; captured admission observation matches the completed same connection |
| Cancel before write | A real connected lease is cancelled/collected without a single HTTP byte or response |
| Expire before write | A1ms transport window plus2ms fixture scheduling delay refuses the first HTTP write and retains native cleanup until collected |

The caller driver schedules at1ms for at most5000 turns within a5s monotonic
budget, including cleanup. It uses a2500ms exchange window for ordinary info.
Only this test driver waits. Native call duration and scheduler delays mean the
budget is an acceptance/scheduling bound, not a hard realtime response guarantee.
The production helper advances once per call and never waits for completion.

Every returned owner replaces a retained fixture slot before any assertion.
Cleanup loops only use that exact lease. A subsequent fixture refuses to replace
an owner whose cleanup is still pending. If the budget expires, the owner remains
retained and cleanup_complete is false; tests fail without discarding cleanup
capabilities or claiming Engine absence. No old copied retention value is used as
an independent reader. Observation/body facts are captured before closure;
assertions follow attempted actual collection, and the postclose getter must fail.

These fixtures do not qualify partial kernel writes, CancelIoEx races, disconnect
faults, hijack transfer, exec effects, live input, resize, process termination,
performance/RSS or arbitrary server responses. Codec pure vectors cover strict
HTTP/media/framing and leftover handling separately. Real broker composition must
validate installed policy/request/scope and Host one-use proofs before effects;
transport metadata and observed info alone confer no execution authority.
