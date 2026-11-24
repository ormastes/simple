/*
 * rt_opengl_* / rt_oneapi_* -- interpreter/seed-only satellite copy.
 *
 * Canonical source: the same 32 function bodies also live in
 * runtime_native.c ("Optional hosted backends are unavailable in the core C
 * runtime" / "OpenGL backfill (unavailable in core C runtime; fail closed)").
 * runtime_native.c is what native product builds link (see
 * src/compiler/70.backend/backend/runtime_compiler.spl, "runtime_native" in
 * its default source list) -- that path is unaffected by this file.
 *
 * This file exists ONLY because the interpreter/seed crate
 * (src/compiler_rust/runtime/build.rs) cannot compile the whole of
 * runtime_native.c: ~22 of its ~470 other symbols (rt_host_gpu_lane_*,
 * rt_host_gpu_queue_*) already have real definitions in that crate's own
 * host_gpu_lane.rs and duplicate-symbol at link time if the whole
 * translation unit is pulled in. Before this file, rt_opengl_ / rt_oneapi_
 * had no C definition reachable from the interpreter at all, so every call
 * died with "unknown extern function: rt_opengl_init" -- indistinguishable
 * from "no GL support" when the real defect was a missing link, not a
 * missing capability. See
 * doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md
 * lane R2.
 *
 * `rt_file_is_char_device` USED to be copied here for the same reason, but
 * it was a DUPLICATE with an INCOMPATIBLE ABI: this copy took a single
 * NUL-terminated `const char*` while the compiler emits, and the Rust
 * runtime's own canonical definition
 * (compiler_rust/runtime/src/value/sffi/file_io/metadata.rs) accepts, the
 * two-argument `(ptr, len)` form (runtime_sffi.rs, text_extern_abi.spl).
 * Under -z muldefs this copy silently WON in the seed/JIT and received a
 * non-NUL-terminated pointer, so `/dev/zero` and `/dev/null` reported as
 * NOT char devices.  The Rust definition now provides the symbol; do not
 * re-add a C copy here.  See
 * doc/08_tracking/bug/rt_file_is_char_device_dejit_and_dual_abi_2026-08-10.md
 *
 * Both families are fixed-value capability stubs (no real GL or oneAPI/SYCL
 * binding exists anywhere in this tree). The 32 bodies live ONCE in
 * runtime_hosted_backend_stubs_impl.h, which this file and runtime_native.c
 * both include, so the two lanes cannot drift apart.
 */

#include <stdint.h>
#include <stdbool.h>

#include "runtime_hosted_backend_stubs_impl.h"
