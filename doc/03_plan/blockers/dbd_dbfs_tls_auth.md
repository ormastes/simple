# dbd production-service closure status

The non-bootstrap service path is implemented. `DbdProvisioningOwnerV1`
validates bounded AUTH tokens, certificate chains, and private signing keys;
retains only the credential digest after admission; wipes/revokes material on
failure and close; and supplies the typed `Tls13ServerConfig`. `DbdDbfsAdapter`
admits only a device-backed `DbFsDriver` whose serialization owner is live,
recovers `/DBD.LOG` through that driver, and acknowledges replacement only
after the driver's namespace commit and backing-device `fsync` succeed. The
listener derives readiness from those owners and fails closed otherwise.

The one intentional external gate is bootstrap provisioning: target boot code
must obtain authenticated certificate/key/token bytes from its platform secret
source and call `DbdServer.provision_service` before replay/bind. This lane does
not invent a firmware key store or embed credentials in the image. Optimized
native zeroization/disassembly and per-target receipts remain release evidence,
not missing application logic.
