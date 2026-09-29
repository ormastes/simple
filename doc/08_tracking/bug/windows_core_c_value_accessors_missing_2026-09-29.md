# Core-C media providers require missing legacy value accessors

## Actual failure

Windows cycle5 source e1e32cdb0c1bab802ab189c8fc98f28cdbc28ec8 rebuilt
1061 modules and linked the Phase2 compiler successfully. Its real positional
hello compiled but lld-link reported exactly these missing symbols:

- spl_array_get_i64: runtime_glfw.obj rt_glfw_present_argb and
  runtime_sdl2.obj sdl2_core_pixel_at.
- spl_as_float: runtime_audio.obj rt_audio_play_pcm_f32.

The preserved rejected compiler SHA256 is
4ada181cfb10d3a6f8efa1bba5bcdb53e9152db6180e27e2d23439523f5e8fac.
Hello log SHA256 is
ecc17bc33dae8ec9f0c7321e09fe828c1503f22560f9cbd9a885a00cd52e57ed.
Canonical exit2 means no admission, hello execution or Phase3 result.

## Owner and correction

runtime_compiler.runtime_core_c_sources_v1 selects runtime_legacy_core.c and
the real media providers while deliberately excluding runtime.c, whose broad
exports collide with other selected owners. runtime.h declares both accessors;
runtime.c defines them, but the selected narrow legacy provider omitted them.

Add the real operations to runtime_legacy_core.c: return the stored double
payload, and perform the existing legacy array lookup before reading its i64
payload. The latter retains that owner's null/out-of-bounds nil behavior. No
monolithic provider, media stub, foreign archive or invented constant is added.

## Verification and reuse plan

The C selfcheck links the real provider and verifies full-width signed integer
values, null/bounds handling and floating by-value ABI including negative zero.
It has not run yet. The actual rejected Phase2 image can compile hello against
the corrected runtime source through the existing SIMPLE_PROJECT_ROOT owner;
its image and retained native cache must remain hash-bound and unmodified.
This diagnostic alone does not admit a rebuilt compiler.

Windows runtime_compiler._runtime_object_cache_dir explicitly returns empty,
and the failed sanity cleaned its temporary C objects. Recompiling those C
providers is therefore required for the minimal proof. The retained 1061
compiler objects and Cargo targets remain available for the separately
authorized cached Phase2 rebuild wherever canonical keys match. No cache
identity may be rewritten and no clean rebuild is requested. Persistent
Windows C-object caching is a separate performance issue, not part of this fix.
