# Identity-store digest and leaf roles V1

Status: **AUTHORED_NOT_RUN**, mirrored manually from
`test/01_unit/lib/io/host_identity_store_leaf_v1_spec.spl`. No test/compiler ran.

The production grammar accepts exactly 64 lowercase hexadecimal stem bytes,
followed by one distinct suffix: .key (68 total bytes), .hosts (70), or .profile
(72). The executable examples use the same complete stem for all three roles,
require all three spellings to validate, and compare the complete names as
distinct. No suffix translates into another role.

Negative examples reject uppercase and non-hex stems, short/long stems,
uppercase suffixes, combined suffixes, traversal, trailing dot/space, NUL,
alternate streams, backslash children and unsupported .sdn/.json roles. They
call the production helper directly without fabricating filesystem owners.

This validates only the authored grammar contract. Native persistence, private
permissions, crash/close effects and role-independent no-replace publication
are covered by the separate authored actual-OS fixture/manual, all NOT_RUN.
Storage never parses profile SDN or chooses the profile's semantic digest;
the consumer derives its .profile stem from canonical strict profile SDN.
