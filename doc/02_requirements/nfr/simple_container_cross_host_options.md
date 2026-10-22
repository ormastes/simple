<!-- codex-research -->
# Simple Container cross-host NFR options (selection pending)

Select one evidence and performance target set with a feature option. The 2026-09-06 orchestrator research records no measured startup/RSS baseline, so absolute runtime budgets should be frozen after a live baseline. All options require bounded receipts/transport, exact native identity, failure cleanup, and no production compilation at startup.

| Option | Description and measurable gate | Pros | Cons | Effort |
|---|---|---|---|---|
| N1 — contract and preflight | Pure admission/SDN round-trip tests pass; fixture receipts state `launch_capable=false` unless backed by a live qualified provider. Record warm probe, startup, and max RSS baselines on each available host. | Fast early truthfulness and stable wire contract. | Does not qualify live host support. | S, about 2–4 test/receipt files. |
| N2 — live per-host qualification | N1 plus one real create/start/wait/destroy cycle per advertised host/isolation tuple; prove identity, host/image compatibility, privilege route, requested limits/network, and fresh exact-ID absence after teardown. Record p50/p95 warm launch and request latency, max RSS, and cleanup failures on fixed fixtures. | Support claims rest on executable evidence. | Needs maintained Windows Server, Linux, and FreeBSD runners and admitted images. | L, about 8–15 fixture/harness files. |
| N3 — recovery and security qualification | N2 plus client/provider crash, reboot/reconnect, duplicate request, stale identity, denied privilege, mismatched image/isolation, and orphan cleanup tests; compare latency/RSS with a versioned baseline and require explicit acceptance of regressions. | Covers durable operation and authority failures. | Most expensive CI and host lab; first baselines still need measurement. | XL, about 15–25 fixture/harness files. |

For all options, macOS fixture evidence must prove a native sandboxed macOS process, its actual exit, and cleanup. No pure or scripted fixture counts as a live Linux, Windows, FreeBSD, macOS, or SimpleOS PASS; VM evidence does not qualify Simple Container.
