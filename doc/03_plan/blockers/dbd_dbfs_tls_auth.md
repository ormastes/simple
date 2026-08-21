# dbd bounded safety-slice blockers

This safety slice does not claim DBFS durable commit, TLS, or client
authentication. The freestanding `dbd` entry has no verified boot-reachable
DBFS engine/commit handle, no TLS handshake/provider boundary, and no
authentication identity/credential boundary. Implementing any of these here
would either duplicate storage semantics or advertise an unverified security
property. They therefore remain explicitly `Blocked` in
`DBD_CAPABILITY_STATE` until an owning DBFS/TLS/auth contract and evidence
path are supplied.
