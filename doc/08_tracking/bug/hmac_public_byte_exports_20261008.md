# Public HMAC byte exports missing

Status: source repair and regression spec authored; Simple execution UNRUN.
Requirement: REQ-HMAC-PUBLIC-BYTES-001.

Phase3 module tls12_prf failed HIR with `module std.crypto.hmac has no exported
item hmac_sha384_bytes` under source6bf and producer b467. The common HMAC
implementation defines it, but the public forwarding module omitted it.
The existing hmac_rfc4231_spec also imports the omitted hmac_sha512_bytes.
The fetched release340c3106 has the same forwarding omission.

The repair exports both existing implementations without changing algorithms,
allocation or ABI. The public import regression checks output lengths and fixed
known-answer bytes for a 20-byte 0x0b key and ASCII Hi There. Expected SHA384
and SHA512 bytes were independently confirmed with .NET HMACSHA384/HMACSHA512;
this is oracle evidence, not a Simple test PASS.

Run the new public-export spec and existing TLS12 PRF and HMAC known-answer
specs through a qualified pure-Simple test binary before claiming runtime
validation. Existing frozen builds are unchanged; apply at the next source
boundary. Retained failure evidence is indexed by
build/rc1-phase3-jobzero-resume40/failure-triage-snapshot.json.
