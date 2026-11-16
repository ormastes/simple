# Windows service namespace V1 source specifications

Status: **NOT_RUN**. Source-authored manual; no generated/runtime PASS claimed.

Source: `test/01_unit/lib/io/windows_service_logon_namespace_v1_spec.spl`.
Five cases call helpers actually used by the native producer:

1. Strict existing `\GLOBAL??\drive:\...` spelling admits a valid root and
   rejects ordinary/alternate namespaces, slashes, traversal, ADS, trailing
   component aliases, DOS devices and embedded NUL.
2. Unicode suffix data is preserved without path or namespace normalization.
3. Direct HarddiskVolume root is accepted; empty, suffix, network, alternate
   namespace and embedded-NUL targets are rejected.
4. Only actual Service5 with every SID/AuthId/session correlation succeeds;
   interactive/network/batch and each mismatched correlation refuse.
5. Unrelated read/control rights do not imply mutation; directory/link and
   standard/generic mutation rights are included in the production deny mask.

These are shape/predicate cases. They do not exercise native ACL parsing,
real LSA facts, namespace custody, cleanup failures or SSH launch.
