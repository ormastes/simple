# Linux same-process executable replacement V1 — consolidated R2

Status: SOURCE_AUTHORED_NOT_RUN, source cycle2. R1 remains immutable at
`/tmp/linux-process-replace-v1-20261115`, including its independent HOLD receipt.
R2 addresses all three source P1s together, introduces scoped bounded image
pinning for the real executable-size requirement, and explicitly ports the
kernel ABI to native LP64 little-endian x86_64/AArch64. Neither architecture has
been compiled, linked, run or qualified by this work.

## Interface and actual authority boundary

Module `std.nogc_sync_mut.io.linux_process_replace_v1` exports opaque
`LinuxProcessReplaceOwnerV1`, request/turn and:

- `linux_process_replace_open_v1(request, cwd)`: BORROWS caller's independently
  owned checkout-directory owner. Returns that ORIGINAL in `turn.cwd`
  IMMEDIATELY, including when `turn.owner` is Some. The replacement registry
  privately owns only a validated independent native duplicate. Caller may close
  the returned original during preparation; it cannot close the private copy.
- `linux_process_replace_prepare_step_v1(owner)`: one bounded copy/hash chunk
  or fixed-size seal/header phase; outer phase stays `preparing` until `ready`.
- `linux_process_replace_replace_v1(owner)`: one execveat attempt; success never
  returns. Every returned turn is failure/refusal, never AgentReady.
- `linux_process_replace_close_v1(owner)`: restores failed execution state and
  closes its private duplicate/image/source/resources. NEVER returns or closes
  caller's original cwd. Closed aliases return no second handback or native work.
- `linux_process_replace_cwd_identity_v1(owner)`: actual private-held directory
  identity DATA for correlation/qualification; cannot construct cwd authority.

Request fields: absolute `program`, signed expected lowerhex64 `expected_digest`,
exact `expected_size_bytes`, approved `max_image_bytes`, `architecture` equal to
`linux-x86_64` or `linux-aarch64`, FULL `args:[text]` including argv0, complete
ordered `environment:[text]`, original `expires_at_unix_ms`, container-local
`preparation_started_ns`, unchanged `preparation_budget_ns`.
Size checks require64<=expected<=max<=536870912. The expected size/digest/ISA and
argv/env/cwd come from the actual protected executable profile and original
signed full invocation, not a wrapper lookup or caller DTO grant. Lower DATA
validation rejects NUL/invalidUTF8, duplicate env names, LD_* overrides and native
argument bounds. It does not authorize an image, environment, workspace or grant.

Turn fields: `owner?`, `cwd?`, `phase`, `facts_known`, `exec_attempted`,
`descriptor_table_isolated`, `filesystem_context_isolated`, `cwd_changed`,
`cleanup_pending`, sticky first `error`. Unknown/foreign-origin lookups preserve
the exact opaque token with `facts_known=false`; default booleans are NOT effect
facts. Early successful unshare has irreversible FD/FS isolation, reported even
on a later origin/bound/admission refusal with no native resource owner. A
pre-effect shape/ISA/unshare refusal returns caller cwd without admitting owner.

## Admission order and copied-directory custody

The earliest native admission syscall is
`unshare(CLONE_VM|CLONE_SIGHAND|CLONE_THREAD|CLONE_FILES|CLONE_FS)` (69376).
VM/SIGHAND/THREAD are actual kernel NONSHARING VALIDATION, not a VM split:
`check_unshare_flags` refuses a nonempty thread group, shared sighand and shared
address space. This excludes separate-TGID VM/sighand peers that TGID task
counting cannot detect. FILES/FS actually split their contexts. This occurs
BEFORE the replacement registry, lifetime resources, original image fd, cwd
copy, memfd or hashing. No syscall fallback or caller nonsharing boolean exists.

After this gate, existing native-mode/genuine procfs/main-thread/fork/PID-namespace
origin checks precede every registry entry, including tombstones. Only one active
owner and at most4096 nonreused bounded tombstones are admitted. Every acquired
fd/allocation is installed in canonical slot/generation state before fallible
classification. Public owner copies do not copy mutable progress or cleanup.

The two real RetainedDirectoryOwner producers (trusted-root traversal and actual
stage-directory opening) privately capture immutable inode/device birth identity
before yielding. Metadata failure leaves the existing fd owner returned, but an
empty birth identity refuses this NEW cwd-admission seam. New package-only
`duplicate_as_process_cwd_v1` checks actual original metadata against that private
birth identity, performs F_DUPFD_CLOEXEC(min3), then checks actual duplicate
identity/type. Any post-dup failure returns that actual duplicate with its error;
the replacement state publishes it before classification and retains cleanup.
The private copy is never exposed to caller aliases. `enter_as_process_cwd_v1`
revalidates birth identity and fchdir acts on that private original retained fd.
No raw caller fd/digest constructor, fd getter or cwd path reopen is added.

Caller must not create NEW CLONE_FILES/CLONE_VM/sighand sharing during admitted
preparation. Early isolation is not a perpetual seal against same-process native
code creating new sharers, closing arbitrary private integers, ptrace or memory
corruption. The approved bootstrap remains the trusted actual caller; no new Git
helpers/native peers may be created after this admission. Original source-root,
parent/exclusion/quota owners stay outside this borrowed child-directory seam.

The former flag helper bodies move mechanically to `retained_file_flags_v1`:
values/configured branches/call sites are unchanged. This keeps retained_file
below800 lines with the separately owned empty-directory delta; no policy or
stage method is removed to hide the file limit.

## Scoped bounded sealed image producer

The existing generic `process_ops.process_pin_executable`/runtime pin has a HARD
64MiB limit. It cannot admit the actual installed Codex file in the root's mapping:
AArch64 ELF290069784 bytes, SHA256
`3bb41c9a80187773e2a59278d4fc355b1a163c31bb5a79581e37d4fe428af047`.
That read-only local metadata is not container/image/runtime qualification.
R2 does NOT raise the generic limit, call private acquire, edit C or add rt exports.

The scoped canonical producer uses ordinary documented libc ports:

1. Open approved absolute source nofollow/nonblocking, retain its actual fd,
   statx identity/revision, regular executable type and EXACT expected size.
   Fixed max512MiB bounds policy. Privately create sealing-capable CLOEXEC memfd.
2. Each preparation turn checks the ORIGINAL deadline, preads at most64KiB from
   retained source at explicit offset and attempts one pwrite. Only the actual
   returned positive accepted count advances the production copy reducer. A
   partial prefix keeps the same buffer/remaining suffix/offset through turns;
   no completed prefix is written again. Errors retain source, partial memfd,
   native arrays and context facts; no hidden new producer/retry exists.
3. Revalidate retained source identity/revision/size and actual target size,
   check deadline again, set0500, add WRITE/GROW/SHRINK/SEAL and query all4 actual
   seals. Then read the ACTUAL sealed image's64-byte ELF header: ELF64/LE/version,
   ET_EXEC/ET_DYN, e_machine62/183 matching actual target, header/PH size/count and
   bounded PH-table range. Scripts/foreign machine/invalid headers refuse.
4. Only after full copy and all4 seals, stream SHA256 from the ACTUAL sealed fd,
   not source path or source bytes. Shared package-only
   `linux_replace_sealed_hash_read_v1(fd,buffer,offset,expected_size)` returns at
   most64KiB actual bytes, checking real seals and regular0500+nlink0/exact-size
   metadata. nlink0 is a specific sealed-memfd policy, not a general deleted-file
   exception. Actual owner retains fd and canonical Sha256StreamV1 state; helper
   mints no public digest/evidence authority. Final expected digest gates ready.

Source copying and hashing do not allocate a whole image in user memory.
Kernel memfd pages consume the FULL expected image size under the original
contained accounting. Scratch arena70400 bytes, bounded native argv/env<=1MiB
plus pointer tables, managed hash/copy arrays and existing runtime all count in
bootstrap memory; their actual footprint/latency remain unqualified. One partial
pwrite can make less progress; deadline and finite caller turn budget govern
termination. No whole290MB managed byte array or cached-path substitution exists.

## Genuine size/memory producer integration gate

The agreed producer is AgentExecutableProfileV1: architecture, exact image size,
max<=512MiB, bootstrap_memory_bytes, agent_memory_bytes. Protected installed V2
profile/layout approval binds it. NEW full InvocationManifestV2 embeds that exact
profile without widening immutable V1 bytes. Host rederives protected value and
checks actual original Host allocation and actual container projection memory
against checked size+bootstrap+agent+65536 BEFORE staging/start. Bootstrap memory
must include the256MiB Git peak AND the buffers/native arrays/runtime above.

These numeric fields are DATA, not a capacity grant. `max_image_bytes` does NOT
reserve memfd memory and cgroup OOM enforcement is not admission. Until those
actual versioned producer/budget checks and signed consumer mapping are present,
composition MUST refuse before this producer, not fabricate proof from local
file size, hashes or request limits. This isolated lower source does not edit or
claim completion of Host/source/workspace/full-manifest owners. Their integrated
source and native qualification remain separate prerequisites.

## Exact replacement and failure lifetime

At replacement, check unchanged deadline; block catchable kernel signals and
recheck genuine origin under that mask. Observe genuine PROC_SUPER_MAGIC task
fd with bounded dirent parsing/EOF and require actual main task. Then REPEAT
kernel VM|SIGHAND|THREAD validation under blocked signals BEFORE disposition
save/reset; a task scan alone is insufficient. Preserve SIG_IGN, reset actual
caught handlers to SIG_DFL, retaining all original kernel snapshots. Normal
runtime startup really installs SIGSEGV/BUS handlers, so default-only fiction is
not used. Raw kernel paths include libc-internal signals32/33.

Save actual current kernel cwd as retained `.` fd. Final close_range(3,UINT_MAX,
UNSHARE|CLOEXEC) seals every nonstdio descriptor for successful exec, including
pin, source, original/duplicated cwd and process-origin descriptors. No inherited
FD allowlist or manual /proc fallback. Enter privately held cwd, recheck original
expiry/budget, restore original mask while dispositions remain default/ignored,
mark attempted BEFORE ordinary libc execveat(fd,"",argv,env,AT_EMPTY_PATH).
Success never returns; there is no fork, original-path/proc fallback or second
attempt. libc must actually provide execveat/memfd_create and kernel/security
policy must admit these effects; Linux5.11+ CLOEXEC support alone is not native
qualification (including executable-memfd policy and seccomp).

Failed exec reblocks, restores saved actual cwd and ALL original dispositions,
then original mask. Partial restoration retains originals and the actual owner;
mask is not unblocked during partial disposition restoration. Close retries only
restoration/cleanup, never exec or original-path pinning. Generic stale/foreign
errors are not retirement proof. Linux close failure is ambiguous: retain opaque
owner/diagnostic and NEVER retry its consumed/reusable integer. Positive cleanup
clears native arrays, source/hash/request refs and private cwd; tombstones retain
bounded facts/first diagnostic only. Original caller cwd is never closed here.
FD/FS isolation is irreversible even after restoration, so a failed bootstrap
exits failure rather than claiming full rollback or new grant.

Sealed main-image SHA is NOT PT_INTERP/DT_NEEDED closure attestation; actual
approved immutable image policy binds loader/libraries/libc/runtime. Original
Host/container/group owner, reservation, exclusion and absolute workload deadline
remain unchanged across exec. AgentReady still requires actual original-workload
image/argv observation (pidfd/start identity/cgroup/namespace); same PID, a preexec
marker or Git success is insufficient. No Input/Geometry lease is minted here.

## Authored evidence and qualification

Fifteen pure production-helper cases and three actual native image/cwd/alias
specimens are authored, ALL NOT_RUN. They cover exact290069784 metadata,
>64MiB/512MiB/overflow/wrong-ISA refusal, actual partial-prefix arithmetic,
hash-after-seal predicate and copied-directory close/open during preparation.
No pure metadata case runs Codex or fabricates a native write/seal result.

Dedicated-process acceptance remains NOT_COVERED/NOT_RUN: actual290MB ELF exec
and argv/env delivery; original workload/deadline unchanged; actual CLONE_FILES
peer unable to replace admitted image; actual separate-TGID VM/sighand peer
refused BEFORE either handler table changes; real concurrent creation refusal;
source mutation, partial write faults, signal arrival/restoration faults, FD/CWD
close faults, all nonstdio close-on-exec, preserved stdio, unsupported security
policy, original path replacement and actual AgentReady observation. Native test
runner is never replaced. Neither local file presence nor architecture-map ACK
is source acceptance, compiler/link PASS or real container qualification.

## Pinned semantic references

- Linuxv6.12 kernel/fork.c blob22f43721d031d48fd5be2606e86642334be9735f,
  check_unshare_flags/ksys_unshare and
  [unshare semantics](https://www.man7.org/linux/man-pages/man2/unshare.2.html):
  [revision](https://github.com/torvalds/linux/blob/v6.12/kernel/fork.c).
- Linuxv6.12 [generic syscall UAPI](https://github.com/torvalds/linux/blob/v6.12/include/uapi/asm-generic/unistd.h)
  blob5bf6148cac2b93e36f362236545e2e6eb473d5ff; x86 syscall table
  blob7093ee21c0d1c0410dbf17a77cb70a6bc6736f04.
- Linuxv6.12 ARM64 signal.h blobbdf0cfb046c94acdc79f68f19d2086d1ca3060b0
  defines SA_RESTORER before generic signal.h blob0eb69dc8e5722f8d4ac55cfe9a9fd59c82acaef4:
  BOTH LP64 action layouts handler/flags/restorer/mask=0/8/16/24, total32, mask8.
- glibc2.40 AArch64 arch-syscall.h blob7ee8a2167aaae172ec910864b6b400fbddb36058;
  public sigaction blob811062ae969a58755a0d6b1c822f5abe2dcc0b21 and pthread_sigmask
  bloba39f3ca33537ac9fa4dc87102c24dd8400e2ec3c suppress internal signals, so raw
  kernel mask/disposition coverage is retained. Syscalls x86/ARM:
  unshare272/97, sigaction13/134, procmask14/135, getdents217/61, close_range436.
- Linuxv6.12 dirent.h blob99002220cd452646b924f76f3c37909d804a67d4 and elf-em.h
  blobef38c2bc5ab7a58ba03d309654051b25a2ac2933; existing target-aware anchored IO
  flags/statx/process-origin primitives remain the source of reused mechanisms.
