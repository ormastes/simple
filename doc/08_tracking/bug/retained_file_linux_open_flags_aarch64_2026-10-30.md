# Retained file legacy open flags use the wrong Linux ABI on AArch64

Status: fixed; focused AArch64 native fixture passed. The x86_64 branch is
source-reviewed but was not executed in this verification.

## Finding

`retained_file_open` and `retained_directory_is_real_no_follow` previously
passed x86_64 Linux flag words to libc on every Linux target. On AArch64,
`O_DIRECTORY` is `0x4000` and `O_NOFOLLOW` is `0x8000`; on x86_64 those bits
are `0x10000` and `0x20000`. The old directory word `720896` therefore
contains `O_DIRECT` rather than `O_DIRECTORY` on AArch64, and the old readonly
word `657408` does not contain AArch64 `O_NOFOLLOW`. This can reject ordinary
directory opens and can follow a final symlink in the legacy retained-file
API.

The affected source was `src/lib/nogc_sync_mut/io/retained_file.spl` at the
Linux branches of `retained_file_open` and `retained_directory_is_real_no_follow`.
The new directory-owner path had already exposed the ABI difference: its
first AArch64 trace used `720896` for `/` and received `EINVAL`; the corrected
owner path uses `573440` for directory opens and `559104` for readonly file
opens. Host syscall tracing after the shared-helper repair confirmed the root
and component opens carry `O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC`, and the retained
leaf open carries `O_NOFOLLOW|O_NONBLOCK|O_CLOEXEC`.

## Repair and regression coverage

Private Linux flag helpers now provide reviewed words for AArch64 and x86_64;
unsupported Linux architectures return zero and fail closed. The retained
owner, legacy file open, and final-directory probe all use the same helpers
and `openat`. Exclusive creation adds `O_WRONLY|O_CREAT|O_EXCL` to the
architecture-correct nofollow, nonblocking, close-on-exec file flags. Windows
behavior is unchanged.

`test/fixtures/retained_file_legacy/main.spl` exercises the public legacy API
with a real regular-file read, leaf-symlink rejection, real-directory and
symlink probe cases, exclusive-create refusal with a content-preserving
readback, and FIFO refusal. The standalone native fixture passed all eight
checks on AArch64. Its trace shows `ELOOP` for the file symlink, `ENOTDIR` for
the directory symlink, `EEXIST` for exclusive creation, and `O_NONBLOCK` on
the FIFO open before `statx` identifies it as `S_IFIFO`. The trace SHA-256 is
`a95eddd7e8b8c1ad9a33409b9d1e737d58593053b88c3fb5322cd0adff92eb18`; build and
runtime receipts are under `build/retained-directory-owner-20261030/cycle8/`.
The separate retained-directory-owner fixture passed its eight path-owner
checks. These focused fixtures do not qualify the broader replay-policy or
pinned tool-chain flow.
