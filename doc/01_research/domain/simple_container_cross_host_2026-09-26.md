<!-- codex-research -->
# Simple Container cross-host: domain research (2026-09-26)

Sources were checked on 2026-09-26. These are platform capabilities, not proof that this repository has implemented or qualified them.

## Windows Server

Microsoft documents two Windows container isolation modes. Process isolation shares the host Windows kernel and is a real native container; Hyper-V isolation gives each container a VM and guest kernel. The mode must be explicit in the capability receipt. Windows Server defaults to process isolation, while Windows client defaults differ and client process isolation is documented for development/testing. [Microsoft isolation modes](https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-containers/hyperv-container).

`runhcs` communicates with Host Compute Service and can run Windows process containers or Hyper-V containers; containerd is a lifecycle integration path. An adapter should observe the actual HCS/runtime compute identity and isolation mode instead of inferring them from a CLI name. [Microsoft Windows container platform](https://learn.microsoft.com/en-us/virtualization/windowscontainers/deploy-containers/containerd), [HCS API reference](https://learn.microsoft.com/en-us/virtualization/api/hcs/reference/apioverview).

Process isolation has a Windows host/base-image compatibility matrix, so admission must pin and check the actual tuple; it cannot silently switch to Hyper-V on mismatch. Microsoft also states process-isolated containers are not a robust boundary for hostile multitenant workloads; Hyper-V isolation is the stronger boundary. [Microsoft version compatibility](https://learn.microsoft.com/en-us/virtualization/windowscontainers/deploy-containers/version-compatibility), [Microsoft container security](https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-containers/container-security).

## Linux

Podman documents non-root execution through a user namespace with subordinate UID/GID ranges in `/etc/subuid` and `/etc/subgid`. Rootless storage and networking have host prerequisites; current documentation identifies `pasta` for a separate network device and notes filesystem limitations. Rootless is therefore a probed host capability, not a property inferred solely from the installed `podman` command. [Podman manual, rootless mode](https://docs.podman.io/en/stable/markdown/podman.1.html).

Podman's rootless API service is tied to a user socket; the API grants broad execution as that user. A shared admin socket is not equivalent to an unprivileged client. [Podman system service](https://docs.podman.io/en/latest/markdown/podman-system-service.1.html).

## FreeBSD

FreeBSD's OCI runtime specification maps OCI containers to the jail subsystem and defines jail/VNET-specific configuration. The FreeBSD Handbook documents Podman, ocijail, storage, `fdescfs`, and PF setup. It explicitly says: “At present, all Podman containers on FreeBSD must run as root, as FreeBSD jails require this.” A rootless Linux Podman policy cannot be copied to FreeBSD. [OCI FreeBSD runtime specification](https://github.com/opencontainers/runtime-spec/blob/main/config-freebsd.md), [FreeBSD Handbook: OCI Containers](https://docs.freebsd.org/en/books/handbook/containers/).

The Handbook also notes that a jail userland cannot be newer than its host and warns that `allow.*` grants loosen isolation. FreeBSD's Linux-emulation examples do not promise that arbitrary Linux images work; systemd/PID 1/kernel-interface dependencies may fail. [FreeBSD Handbook: Jails](https://docs.freebsd.org/en/books/handbook/jails/), [FreeBSD Handbook: OCI Containers](https://docs.freebsd.org/en/books/handbook/containers/).

## macOS and SimpleOS

Apple's Containerization project executes Linux containers inside lightweight VMs, one per container in its documented design. A macOS fixture using this route proves a macOS-hosted Linux VM container, not a Darwin native container. [Apple Containerization](https://github.com/apple/containerization), [Apple container technical overview](https://github.com/apple/container/blob/main/docs/technical-overview.md).

SimpleOS's `ContainerRuntime` is a separate OS-kernel path in this repository. Its current scheduler-bound launch and exit observation can share copied lifecycle values with hosted providers, while scheduler authority, native handles, and mutation stay in the SimpleOS adapter. This is a local design inference from the code map, not an external platform claim.

## Consequence for admission

An exact `(host_os, guest_os, isolation_class, provider_id)` match and a proven privilege route are necessary before `launch_capable=true`. `user` can describe qualified Linux rootless Podman. `delegated` can describe a client using a narrowly authorized Windows/FreeBSD broker only after that broker exists and is tested. `unavailable` is required when the launch authority or live provider is missing. Capability discovery and scripted tests must not be reported as live host qualification.

## 2026-09-27 process-only Windows and native macOS correction

The user selected **Windows Server process isolation**, which shares the host
Windows kernel, and excluded Hyper-V/VM execution from Simple Container.
Windows Server defaults to process isolation; reject an explicit Hyper-V mode
and a version-incompatible process-isolated image instead of changing modes.
[Microsoft isolation modes](https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-containers/hyperv-container),
[version compatibility](https://learn.microsoft.com/en-us/virtualization/windowscontainers/deploy-containers/version-compatibility).

Use containerd → runhcs → HCS as the initial Windows platform path. HCS
compute-system identity and process handles stay inside the provider. Container
feature/runtime readiness is separate from client authorization. A process
container does not require the Hyper-V role; a non-admin client still needs an
explicit, scoped authority route. Docker's named-pipe access is commonly
Administrator-only by default, and broader pipe access is not itself a
workload-scoped policy. [Microsoft containerd](https://learn.microsoft.com/en-us/virtualization/windowscontainers/deploy-containers/containerd),
[HCS overview](https://learn.microsoft.com/virtualization/api/hcs/overview),
[system requirements](https://learn.microsoft.com/en-us/virtualization/windowscontainers/deploy-containers/system-requirements),
[daemon access](https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-docker/configure-docker-daemon).

Use a compatible immutable Windows image and default workload identity
`ContainerUser`, with explicit mount ACLs. Microsoft does not present process
isolation as its strongest hostile-multitenant boundary. These limits belong
in the provider capability and deployment policy.
[Container security](https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-containers/container-security),
[persistent storage and ACLs](https://learn.microsoft.com/en-us/virtualization/windowscontainers/manage-containers/persistent-storage).

The user also corrected macOS: run macOS programs on macOS through a native
sandbox path, and SimpleOS programs on SimpleOS. Apple's Linux container VM
product remains outside this Simple Container route. See
[native Mac research](native_macos_simple_container_2026-09-27.md).
