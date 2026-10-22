# `smf_host_platform_id()` returns 4 (FreeBSD) on Linux under the interpreter

- Status: open
- Found: 2026-10-19, lane work/dynsmf-call-bytes
- Binary: Rust seed `simple-phase3-codec-candidate-20261018/.../target/bootstrap/simple`, sha256 prefix `9c45d2bf601ab93e`, aarch64 Linux host

## Repro

```simple
use os.smf.host_target.{smf_host_arch_id, smf_host_platform_id, smf_target_is_host_compatible}
fn main():
    print "p=" + (smf_host_platform_id() as i64).to_text() + " a=" + (smf_host_arch_id() as i64).to_text()
    print "compat11=" + smf_target_is_host_compatible(1, 1).to_text()
main()
```

`SIMPLE_EXECUTION_MODE=interpreter simple run repro.spl` on Linux/aarch64 prints
`p=4 a=1` and `compat11=false`. Expected `p=1`, `compat11=true`.

## Location

`src/os/smf/host_target.spl:6-13`: four `@cfg(<os>) val SMF_HOST_PLATFORM_ID`
definitions. The interpreter binds the last one (`@cfg(freebsd)`, line 12-13)
instead of the `@cfg(linux)` one. The arch block (`:15-`) resolves correctly
(`a=1`).

## Impact

`smf_dynlib_validate` (`src/os/smf/smf_dynlib.spl`, `smf_target_is_host_compatible`)
rejects every Linux-tagged SMF image in the interpreter with
`smf target mismatch: platform 1 arch 1`. Only platform-Any (0) images load.
`test/01_unit/os/smf/dynsmf_call_bytes_spec.spl` uses a platform-Any fixture
to work around it.
