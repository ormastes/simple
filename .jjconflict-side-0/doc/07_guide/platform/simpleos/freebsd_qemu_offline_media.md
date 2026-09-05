# FreeBSD QEMU offline base-media contract

The FreeBSD bootstrap wrapper uses the same configurable large-artifact root as
the SOSIX QEMU matrix. On this repository host that root is `/mnt/data/.simple`;
other hosts default to `~/.simple`. `SIMPLE_BIG_STORAGE_ROOT` or the workspace
`.simple-big-storage-root` file can override it.

The canonical FreeBSD 14.4 base image is:

```text
<storage>/qemu/images/freebsd/FreeBSD-14.4-RELEASE-amd64-BASIC-CLOUDINIT-ufs.qcow2
```

Supply media from a separately obtained, trusted local file. The expected
SHA-256 is mandatory and must come from an independently trusted FreeBSD
checksum source:

```sh
sh scripts/qemu/simple-freebsd-media.shs --supply /safe/inbox/FreeBSD.qcow2 EXPECTED_SHA256
```

The command verifies the source digest and qcow2 structure before an atomic
copy, then writes an adjacent `.sha256` admission record. It never accesses the
network. A mismatched digest, malformed qcow2, partial copy, missing checksum,
or missing `qemu-img` fails closed.

Check admission and obtain deterministic resume settings with:

```sh
sh scripts/qemu/simple-freebsd-media.shs --check
sh scripts/qemu/simple-freebsd-media.shs --resume
```

Then run the existing wrapper:

```sh
sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke
```

For a noncanonical path, set `QEMU_VM_PATH`; set `QEMU_BASE_VM_SHA256` or place
the trusted digest in `QEMU_VM_PATH.sha256`. The wrapper performs the same
checksum and qcow2 admission during preflight and immediately before boot.
Overlays and cloud-init material remain disposable under
`<storage>/qemu/overlays/freebsd/bootstrap`; the admitted base image remains
read-only and reusable.
