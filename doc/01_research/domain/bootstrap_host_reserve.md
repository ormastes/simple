# Bootstrap host reserve: policy source

This repair implements an existing repository resource policy; no new external
API or allocator behavior is introduced. The authoritative contract is
`doc/07_guide/infra/toolchain/host_config.md` and the commented
`mem_reserve_free_mib` key in `config/host/host_config.sdn`: RAM/commit each build
keeps free on the host. The independently enforced compiler RSS cap is an upper
bound on that compiler tree. These two resource domains must remain distinct.

When host free memory is unknown, retain the established conservative
cap-minus-reserve fallback. When both measurements are absent, retain the
existing declared-budget behavior. Do not lower the configured reserve,
coordinator allowance, worker estimate, or enforced cap to obtain a pass.
