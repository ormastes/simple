# Windows Docker process-provider NFR constraints

Status: source constraints; runtime measurements NOT_RUN.

The selected full-feature plan requires finite execution and bounded retained
state. This source admits positive timeout up to 300000 ms and output between
4096 and 1048576 bytes per stream. It retains at most 64 attempt records; exhaustion
fails closed rather than evicting ownership. Script fixtures are limited to 256
commands and 4 MiB retained bytes. Request command/argument count, field bytes,
canonical record size and CPU/memory limits are checked before execution.

No startup, throughput, latency, RSS or coverage result is claimed. Live probe,
create/start/wait, restart recovery and exact cleanup must record elapsed time,
peak RSS, engine/host/image identity and actual isolation on the admitted Windows
fixture. Bounds are policy ceilings, not measured performance targets. The
process capture provider must report output/deadline limits even for exit zero.

No new broad engine inventory scan, retry sleep, package installation or global
prune is used. The only absence query is a bounded exact full-ID filter after
successful removal. Caller-owned durable persistence and replay checks remain
required independently of the provider's bounded cache.
