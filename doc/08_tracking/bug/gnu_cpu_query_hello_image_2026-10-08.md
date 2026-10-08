# CPU-query Simple Hello image follow-up

This note updates the image-qualification status in
`gnu_cpu_query_constructor_root_2026-10-08.md`; it does not replace the focused
C-query tests or qualify a full bootstrap.

The retained combined-runtime LLVM Hello check completed successfully. Its
artifacts are in `build/item5-enum-subject-repair-20261008/hello-llvm-cpu-query/`
from the qualification workspace. `hello.json` records `status=pass`, gate,
build, and execution exit status 0, and stdout `hello\n`. The resulting ELF is
13,704 bytes, SHA-256
`4a93d5bb59cddf11d5f1dbe6a4d21740f549d5259388a85d2ef59544f359e155`.

Identity recorded by the receipt:

- Simple producer source: `af5e62fb4a37defcda5dc744c3049d812ecaddbf`.
- Compiler: SHA-256 `e134ee9afbc3a32e0d9c66a5a4bab5dc4541eea3e0bc8e9e4f4f420f141c768c`.
- Supplied runtime archive: SHA-256 `6ca86625f7e19bf72eb7c086ca96e3138fbcca71a612d620630ded6bca8ed5b8`.
- Runtime source overlay: commit `930659035510a866280b7f34f960d6d12e624b57`; its four production files are `runtime_simd_case.c`, `runtime_simd_utf8.c`, `runtime_simd_dispatch.c`, and `runtime_simd_dispatch.h`. The overlay receipt also hashes the five related runtime test files.

The matched images were 27,000 bytes at baseline, 19,720 after lazy SIMD, and
13,704 after the CPU-query change. The final symbol census contains no
`__cpu_indicator_init`, `__cpu_model`, or GNU CPU-feature cache symbol. This is
a narrow Linux x86_64 Hello result: it makes no claim about Windows/i386,
full-bootstrap admission, DB/HTTP execution, or application performance.
The warm-ASCII timing regression recorded in the lazy-SIMD report remains
relevant and is not erased by the smaller image.
