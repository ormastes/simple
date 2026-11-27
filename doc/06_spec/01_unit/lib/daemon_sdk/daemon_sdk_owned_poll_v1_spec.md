# Daemon SDK owned poll V1 scenarios

Source: `test/01_unit/lib/daemon_sdk/daemon_sdk_owned_poll_v1_spec.spl`.
Shared oracles: `test/fixtures/daemon_sdk/owned_poll_v1.spl`.
Manual companion; status NOT_RUN. This is not generated execution evidence.

| Requirement | Scenario | Required observable result |
|---|---|---|
| DOWNER-01/02 | Idle then stopped runner with owner counters7/19 | Owner unchanged; idle increments cycle; stopped turn leaves cycle and stopped status unchanged |
| DOWNER-01/03 | Two requests in one serial batch | Returned owner handled2/total5; two real effects/responses; runner items2 and both requests removed |
| DOWNER-01/02 | Response target directory refuses publication | Returned owner handled1/total7; original request retained; publication-blocked state; later callback forbidden |
| DOWNER-01/02 | Handler returns unrelated response identity | Updated owner retained before rejection; no unrelated response published; runner stops |
| DOWNER-01/02 | Handler removes request before checked acknowledgement | Updated owner retained; response exists; acknowledgement-blocked state; next callback forbidden |
| DOWNER-01/03 | Batch limit1 with two queued requests across turns | Each turn handles one; caller writeback accumulates owner; runner items/cycles accumulate |
| DOWNER-01/03 | Second callback refuses response after a successful prefix | Latest owner includes both callbacks; only first item counts/acknowledges; runner stops; later callback forbidden |
| DOWNER-03 | Existing legacy publication-failure oracle through adapter | Captured immutable handler executes once; response refusal stops runner and retains request |

Native subset selects idle/stopped, owned publication-failure and legacy
publication-failure cases only. It does
not establish successful acknowledgement, full SSpec admission or host-service
composition. Async facade identity is source-reviewed; it adds no executor.
