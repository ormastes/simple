# SSH Custom Serial Transport — Domain Research

**Date:** 2026-04-11  
**Feature:** Custom serial communication layer for SSH  

## User Request

> how add custom serial communication layer to ssh

---

## Background: How SSH Transport Works

SSH (RFC 4253) runs above any **reliable, ordered byte stream**. TCP is conventional but not required. The protocol itself is transport-agnostic. The key injection points available without patching OpenSSH source:

| Mechanism | Description |
|---|---|
| **TCP direct** | Default: `ssh user@host:22` |
| **ProxyCommand** | Shell command whose stdin/stdout become the SSH transport pipe |
| **ProxyJump (-J)** | Sugar over ProxyCommand with `-W %h:%p`; tunnels through a bastion |
| **ControlMaster** | Reuses an existing authenticated connection via a Unix socket |

---

## Approach 1: ProxyCommand + socat (Recommended — No Code Change)

OpenSSH executes the `ProxyCommand` string and treats its stdio as the transport socket. `socat` can bridge a serial device to stdio:

```bash
ssh -o ProxyCommand="socat - /dev/ttyUSB0,b115200,raw,echo=0" user@target
```

Or in `~/.ssh/config`:
```
Host embedded-device
    ProxyCommand socat - /dev/ttyUSB0,b115200,raw,echo=0
```

**Requirements:**
- `socat` installed on the host
- SSH daemon (OpenSSH or Dropbear) running on the target with serial as its stdin/stdout, OR target has an IP stack and listens on a port accessible via serial (PPP/SLIP)
- No kernel network stack needed on the host side

**Variant — SLIP/PPP instead of raw serial:**
If the target runs PPP over the UART, the host brings up `pppd` first:
```bash
pppd /dev/ttyUSB0 115200 192.168.99.1:192.168.99.2 noauth local nodetach &
ssh user@192.168.99.2
```

---

## Approach 2: ser2net (Remote Serial Exposure)

`ser2net` exposes serial ports as TCP listeners. Useful when the serial adapter is on a different machine.

```
# /etc/ser2net.conf
2000:raw:600:/dev/ttyS1:115200 8DATABITS NONE 1STOPBIT
```

```bash
ssh -o ProxyCommand="socat - TCP:serial-host:2000" user@target
```

---

## Approach 3: libssh2 Custom SEND/RECV Callbacks

For programmatic control (embedding in an application rather than using the CLI), libssh2 supports full transport replacement:

```c
// Set custom send/recv on the session:
libssh2_session_callback_set(session, LIBSSH2_CALLBACK_SEND, my_serial_send);
libssh2_session_callback_set(session, LIBSSH2_CALLBACK_RECV, my_serial_recv);

// Callback signature:
ssize_t my_serial_send(libssh2_socket_t socket,
                       const void *buffer, size_t length,
                       int flags, void **abstract);

ssize_t my_serial_recv(libssh2_socket_t socket,
                       void *buffer, size_t length,
                       int flags, void **abstract);
```

The `abstract` pointer carries user context (e.g., serial fd). The `socket` parameter can be ignored (pass `LIBSSH2_INVALID_SOCKET` to `handshake`). This approach replaces TCP entirely with any byte channel — serial fd, JTAG FIFO, shared memory ring, etc.

**libssh2 API references:**
- `libssh2_session_callback_set()` — LIBSSH2_CALLBACK_SEND (type 5), LIBSSH2_CALLBACK_RECV (type 6)
- `libssh2_session_handshake(session, fd)` — accepts any fd or LIBSSH2_INVALID_SOCKET when custom callbacks are set

---

## Approach 4: libssh SSH_OPTIONS_FD

The `libssh` library (different from libssh2) takes a simpler approach:

```c
int fd = open("/dev/ttyUSB0", O_RDWR | O_NOCTTY);
// configure termios baud rate, raw mode, etc.
ssh_options_set(session, SSH_OPTIONS_FD, &fd);
ssh_connect(session);  // skips socket creation, uses supplied fd
```

Simpler than custom callbacks but limited to libssh (not libssh2/OpenSSH).

---

## Approach 5: ControlMaster Multiplexing (Optimization)

Not a transport replacement — but critical for **slow serial links**. After the first authenticated SSH connection, subsequent sessions reuse it without re-negotiating crypto (expensive at 9600 baud):

```
Host *
    ControlMaster auto
    ControlPath ~/.ssh/cm-%r@%h:%p
    ControlPersist 10m
```

---

## Approach 6: SLIP (minimal embedded alternative)

For microcontrollers (Zephyr RTOS, FreeRTOS + lwIP):
```bash
slattach -p slip -s 115200 /dev/ttyUSB0 &
ifconfig sl0 192.168.1.1 pointopoint 192.168.1.2
ssh user@192.168.1.2
```

RFC 1055 SLIP has minimal overhead vs PPP. Zephyr has a ready SLIP stack. Once the network interface is up, standard SSH works unmodified.

---

## Use Case Matrix

| Use Case | Best Approach |
|---|---|
| Embedded Linux via UART (no IP stack) | ProxyCommand + socat raw serial |
| Embedded Linux behind serial-to-Ethernet bridge | ser2net + ProxyCommand |
| Microcontroller (Zephyr/FreeRTOS) | SLIP or PPP → standard SSH over IP |
| Custom JTAG/SWD tunnel (OpenOCD RTT) | libssh2 custom SEND/RECV callbacks |
| Industrial PLC with RS-232 | ser2net or direct socat ProxyCommand |
| Programmatic SSH client over serial in Simple | libssh2 custom callbacks via new FFI |
| Bandwidth-constrained link (9600 baud) | ControlMaster to amortize handshake |

---

## Key Tools

| Tool | Role |
|---|---|
| `socat` | Swiss-army byte relay — serial ↔ stdio ↔ TCP |
| `ser2net` | Expose serial ports as TCP servers |
| `pppd` | Full IP stack over serial (PPP) |
| `slattach` | Minimal IP over serial (SLIP, RFC 1055) |
| `dropbear` | Lightweight SSH daemon for embedded Linux |
| `libssh2` | C SSH library with transport callback API |
| `libssh` | Alternative C SSH library with SSH_OPTIONS_FD |

---

## References

- [SSH ProxyCommand with socat — End Point Dev](https://www.endpointdev.com/blog/2013/04/socat-and-netcat-proxycommand-ssh/)
- [OpenSSH/Cookbook/Proxies and Jump Hosts — Wikibooks](https://en.wikibooks.org/wiki/OpenSSH/Cookbook/Proxies_and_Jump_Hosts)
- [OpenSSH/Cookbook/Multiplexing — Wikibooks](https://en.wikibooks.org/wiki/OpenSSH/Cookbook/Multiplexing)
- [Serial ports over TCP/IP with socat — Acme Systems](https://www.acmesystems.it/socat)
- [Serial Programming/IP Over Serial Connections — Wikibooks](https://en.wikibooks.org/wiki/Serial_Programming/IP_Over_Serial_Connections)
- [libssh2_session_callback_set() — libssh2.org](https://libssh2.org/libssh2_session_callback_set.html)
- [libssh2_session_handshake() — libssh2.org](https://libssh2.org/libssh2_session_handshake.html)
- [SSH over Serial Port — Linux Lizard](https://linuxlizard.com/2023/01/30/ssh-over-serial-port/)
- [ttyssh — SSH with TTY/serial port forwarding](https://github.com/b1f6c1c4/ttyssh)
- [Exploring SLIP Networking Over UART with Zephyr — Swedish Embedded](https://swedishembedded.com/developers/connectivity/slip)
