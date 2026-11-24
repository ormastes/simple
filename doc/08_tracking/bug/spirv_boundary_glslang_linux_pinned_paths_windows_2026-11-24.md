# spirv_boundary_glslang_spec: 4 examples need Linux-pinned /usr/bin tools (Windows host)

Found by the sweep-puregpu lane, 2026-11-24, seed `simple-release.exe`, Windows host.

`boundary_spirv_provider.spl` pins `GLSLANG_PATH`/`SPIRV_*_PATH` to `/usr/bin/...`.
On a Windows host none exist, so the provider-descriptor examples that hash the real
glslangValidator binary (4 of 11: hashes real binary, frozen manifest contract,
registry registration, plan-source resolution) fail with "got false". These are
environmental, not a regression; the fixture-backed examples pass.

Fixed in this change: the "regeneration check" example failed because the
candidate/counterpart "not installed at pinned paths" details did not say
`unavailable`, contradicting the spec contract (unavailable, never a pass).

Open: make the tool paths host-resolvable (PATH lookup / env override) or have the 4
descriptor examples report an explicit unavailable-skip when the tools are absent.
