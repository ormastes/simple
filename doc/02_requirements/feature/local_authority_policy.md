# Local public authority policy

This is the approved protected-policy component of the finite local host execution path, not enrollment or a complete host service.

- HOST-LOCAL-POLICY-01: Decode only bounded canonical SDN public verification policy. Reject unknown/private/continuity fields, malformed key encodings and invalid generations. Delegate key role/scope/budget/index validation to the existing authority snapshot owner.
- HOST-LOCAL-POLICY-02: From an independently trusted private root, read only the fixed nofollow regular policy file and compare the externally pinned digest before decoding. Reject nonprivate paths, malformed/unbounded pins, traversal/control characters and symlink roots/leaves. Digest/mode checks must never be presented as authentication of an arbitrary root, boot identity or provider continuity.

Implementation: `local_authority_policy_v1.spl`. The matching executable specification and authored manual map each requirement to real parsing and filesystem assertions. Runtime status remains NOT_RUN until qualified execution evidence exists. Full local host commands additionally need trusted root initialization, live boot/provider identity and durable execution observations.
