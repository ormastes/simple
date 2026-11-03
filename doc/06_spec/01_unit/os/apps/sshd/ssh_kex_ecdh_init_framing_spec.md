# Curve25519 KEX_ECDH_INIT framing

Executable: test/01_unit/os/apps/sshd/ssh_kex_ecdh_init_framing_spec.spl
Status: manually authored companion; six examples, runtime UNRUN.

The server negotiates only curve25519-sha256. Public keys are32 bytes (RFC8731 section3); INIT is byte30 and one SSH string (RFC5656 section4, RFC4251 section5), yielding37 bytes.

1. Preserve all32 key bytes including00/7f/80/ff; accept both strict modes.
2. Reject all37 truncation lengths0..36.
3. Reject inconsistent prefixes0/1/31/33/80/ff and high bits in each upper length byte.
4. Reject complete strings with widths0/1/31/33/56.
5. Reject trailing bytes under strict full-consumption policy.
6. Reject opcodes0/2/4/20/21/31/ff in both strict modes.

Negative cases call both the public parser and live-path validator. Expected outcomes are literal error assertions, not comparisons to another parser. No generated manual, execution PASS, server disconnect transcript or crypto correctness is claimed.
