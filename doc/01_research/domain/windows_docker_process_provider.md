# Windows Docker process provider domain research

2026-11-07. Sources consulted through search; no live host was exercised.

[Docker create](https://docs.docker.com/reference/cli/docker/container/create/)
creates without starting and supports explicit isolation. [Docker run](https://docs.docker.com/reference/cli/docker/container/run/)
documents Windows process and Hyper-V modes. Therefore command construction must
specify process isolation and subsequent inspection must check the actual mode;
a platform label or daemon default is insufficient.

[Microsoft's version compatibility matrix](https://learn.microsoft.com/en-us/virtualization/windowscontainers/deploy-containers/version-compatibility)
distinguishes host/image combinations and describes Windows 11 / Server 2022
process isolation separately. A historical host label does not establish current
compatibility. This provider requires an administrator-selected exact host kernel
version, image OS version, immutable image digest and engine identity; the actual
values must match observations. Selection of a compatible pair and independent
live qualification remain prerequisites. No automatic Hyper-V or WSL fallback is
permitted when the selected process pair fails.

The Docker service is a privileged authority boundary. Access to its pipe is not
proof of per-workload authorization for ordinary independent clients. The initial
leaf is a trusted controller adapter, not an untrusted multi-tenant broker.
