# OpenCL Session Contract Specification

> Manually synchronized on 2026-07-12; no Simple/docgen command ran in this
> session.

The eight scenarios cover fail-closed session initialization, lifecycle,
generated-kernel provenance, argument binding, and readback evidence. The
unavailable-session scenario now also rejects offset writes without an FFI and
rejects negative offsets. Native buffer-size bounds are enforced by
`rt_opencl_write_buffer_at`; C syntax was checked separately.

Source: `test/01_unit/lib/gpu/engine2d/opencl_session_contract_spec.spl`

