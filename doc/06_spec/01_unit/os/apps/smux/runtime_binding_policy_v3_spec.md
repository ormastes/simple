# Fixed runtime binding policy validation

Status: **AUTHORED_UNRUN**. Pure production decoder imports only. Synthetic policy values never enter a native owner or filesystem loader.

Source: `test/01_unit/os/apps/smux/runtime_binding_policy_v3_spec.spl`.

1. Decode policy shape without treating it as a signed grant or host admission. Preserve the complete common broker profile and output resource request.
2. Require the exact trusted configuration schema at every nested boundary. Reject root overrides, additional grant fields, wrong types, and unsupported versions.
3. Reject zero CPU and memory before a provider owner can receive the policy.

The production loader reads only `<verified-host-root>/smux-runtime-policy.sdn` through a bounded regular-file no-follow owner. These pure tests do not verify filesystem protection, broker delegation, helper admission, host capacity, or provider attachment. Those require the real configured owner and qualified runtime fixtures.
