# Native-all atomic-write provider verification receipt

- Date (UTC): 2026-08-29
- Base revision: `ae63a7240c55dc9e561bc9b5d1a526198546a607`
- Command: `sh scripts/check/check-native-all-atomic-write-provider.shs`
- Execution count for this correction: 1
- Result: PASS

## Tool and artifact identity

- C compiler: `/usr/bin/cc`
- C compiler SHA-256: `1b99826121ae6682a634e5efe09bd3e3df58ce58e0b28f849114ab5b89139c26`
- Archive: `/mnt/data/phase1-duplicate-file-atomic-write/src/compiler_rust/target/debug/libsimple_native_all.a`
- Archive SHA-256: `84d4c5ae1483688c3dd7c6ecba861741638001b492e8d8cbebf1b600743eba46`
- Strong `rt_file_atomic_write` provider count: 1

## External C ABI probe

- Link return code: 0
- Link stdout: empty
- Link stderr: empty
- Run return code: 0
- Run stdout: empty
- Run stderr: empty

The external C consumer created path and content `RuntimeValue` strings through
`rt_string_new`, invoked the archive's `rt_file_atomic_write`, verified the
resulting file bytes, and released both values through `rt_string_free` on every
post-allocation exit path. The checker reported:

```text
PASS: native-all has one runtime-owned atomic-write provider and an external ABI consumer links and runs
```
