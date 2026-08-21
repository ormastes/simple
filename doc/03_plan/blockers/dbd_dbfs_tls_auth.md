# dbd production-service closure status

The non-bootstrap service path is implemented. `DbdProvisioningOwnerV1`
validates bounded AUTH tokens, certificate chains, and private signing keys;
retains only the credential digest after admission; wipes/revokes material on
failure and close; and supplies the typed `Tls13ServerConfig`. `DbdDbfsAdapter`
admits only a device-backed `DbFsDriver` whose serialization owner is live,
recovers `/DBD.LOG` through that driver, and acknowledges replacement only
after the driver's namespace commit and backing-device `fsync` succeed. The
listener derives readiness from those owners and fails closed otherwise.

The filesystem-launched combined server now obtains bounded mutable
certificate/key/token buffers from its mounted boot-secret files and calls
`DbdServer.provision_service` before replay or bind. It verifies destruction of
all three source buffers and retains no argv or hardcoded credential path. The
same entry consumes a typed DBFS VFS projection and cannot promote FAT32,
RamFS, a missing sync owner, or a non-transactional rename.

The remaining release gate is target evidence: the kernel must return the
typed mounted-DBFS recovery/durability capability through syscall 79 and the
three architecture receipts must prove TLS AUTH, committed SET/readback after
fresh boot, and optimized-native source-buffer zeroization. No embedded
credential or caller-controlled readiness boolean is an allowed substitute.
