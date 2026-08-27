# SimpleOS primary tool manifest

## Authenticated artifact receipts

Every tool is admitted independently through
`simpleos_primary_tool_receipt_v1`. The signed payload is bounded to 4096 bytes
and binds the tool name, canonical filesystem path, artifact digest, target,
filesystem, behavior contract, receipt id, signing key id, validity window, and
nonce. Verification is Ed25519 against the loader-configured trust root and
fails closed for missing/malformed signatures, unknown keys, stale/future or
overlong windows, invalid targets, and malformed identities.
The verifier owner reconstructs a domain-separated, length-prefixed canonical
body from every typed receipt field. Both the carried payload and any caller
expectation must exactly equal those bytes before signature verification, so an
arbitrary signed payload cannot be attached to substituted metadata. Successful
admission atomically consumes the bounded `receipt_id:nonce` replay key; reuse,
store exhaustion, expiry, and future issuance fail closed.

A verified receipt is not executable authority. The loader must separately
hash the bytes read from the mounted filesystem, compare that digest and all
receipt bindings, consume a live loader-owned authority token, and only then
spawn the process. Source modules, package projections, serial markers, fixed
commands, and host-side execution cannot satisfy this contract. Until those
target artifacts and live receipts exist, canonical manifest rows remain
`Blocked`; this lane makes no bootstrap or guest-execution claim.

`simpleos_primary_tool_manifest_v1` is the closed, versioned declaration for
primary userland categories: administration, archive/compression, networking,
checksums, text processing, process monitoring, and package management.

Rows are declared data, never inferred from source or package presence. A row
may become Supported or Partial only after evidence-service admission records
the exact owner, artifact digest, three target triples, FAT32/DBFS/NVFS
operation evidence, version/help behavior, and negative/error behavior.

The selected v1 inventory is exact and closed:

| Category | Executable identities | State |
|---|---|---|
| administration | no admitted executable | `Blocked` |
| archive/compression | no admitted executable | `Blocked` |
| networking | no admitted executable | `Blocked` |
| checksums | `/usr/bin/sha256sum`, `/usr/bin/md5sum` | `Blocked` |
| text processing | `/usr/bin/grep` | `Blocked` |
| process monitoring | `/usr/bin/ps` | `Blocked` |
| package management | no admitted executable | `Blocked` |

The three executable-bearing blocked categories have real Pure Simple owners
and bounded behavior:
checksum and grep read through `VfsManager.read_bytes_bounded` with a 64 MiB
per-file limit, 64 KiB chunks, and at most 128 files; `ps` consumes the one
`list_tasks` owner, capped at 256 tasks and 32 command arguments. Their package
identities intentionally carry empty artifact-digest and admission-receipt
fields. The launcher returns exit 126 and `loader_authority_state=absent` for
these known files, or 127 for an unknown identity. It never treats that text
state as an executable-authority token and never falls back to an in-process
shortcut, PATH lookup, alias expansion, background execution, or pipeline
execution. The generic `launcher_launch_path_with_args` boundary also rejects
all four canonical paths before process spawn. It compares lexically normalized
absolute paths, so equivalent spellings with repeated separators, `.` segments,
or `..` segments cannot bypass the gate. Async and non-shell launcher callers
therefore cannot bypass the tool-specific gates.

Promotion requires target-native bytes at the exact canonical path, a lower-case
SHA-256 digest of those bytes, an evidence-service admission receipt, and a live
loader-owned `ExecutableAuthorityTokenV1` consumed by the loader. Source
presence, a package record, an empty digest/receipt, or a copied diagnostic
value cannot authorize launch.

## Linux-compatible command surface inventory

This section is the canonical source-derived inventory of command-shaped
SimpleOS functionality.  It is deliberately adjacent to, and does not expand,
the closed seven-category primary manifest above.  In particular, an
implemented shell handler is not a filesystem executable, and an image-builder
deployment identity is not proof that bytes were installed or launched.

The status vocabulary here is narrower than the primary manifest status:

- `shell-builtin` means the interactive shell handles the name in-process;
  there is no executable identity for that command.
- `filesystem-blocked` means a canonical image path and Pure Simple entry owner
  exist, but authenticated guest admission and live loader execution evidence
  are missing.
- `implemented-not-dispatched` means reusable Pure Simple logic exists but no
  shell or SimpleBox filesystem command routes to it.
- `unavailable` means this inventory found no command implementation and no
  admitted executable identity.  A host binary, alias, or host process call is
  never an implementation.

### Shell builtins (not filesystem-launchable)

`ShellApp._is_builtin_command` and `_dispatch_builtin` own this exact in-process
surface:

```text
cd ls list pwd echo cat mkdir rm cp mv find kill run mount clear help exit
env export history hostname uptime dmesg mem reboot jobs fg bg readf touch
head tail wc sort uniq which date uname true false tee ln chmod stat cut tr
sed basename dirname sleep seq expr test [ xargs yes printenv readlink mktemp
diff patch file strings hexdump base64 git jj source . read printf alias
unalias shift trap wait break continue return set mkfifo awk tac rev nl fold
column paste comm join od bc factor shuf numfmt tree less
```

These names have status `shell-builtin` on every architecture on which the
interactive shell itself runs. Their option and error behavior is the owning
`cmd_*` or `tool_*` handler in `src/os/apps/shell/`; there is no aggregate
`--version`/`--help` contract and no `/bin` or `/usr/bin` identity.  `which`
describing one as `shell built-in command` is diagnostic only.  Consequently
none of these rows proves FAT32, DBFS, or NVFS filesystem launch, loader
authority, a target artifact, or execution on x86, ARM, or RISC-V.

Some names overlap filesystem identities below (`echo`, `pwd`, `cat`, `head`,
`wc`, `seq`, `true`, and `false`).  An unqualified shell command selects the
builtin first.  That success must never be recorded as evidence for the
filesystem artifact or its alias.

### SimpleBox filesystem identities (implemented, launch blocked)

The only routed SimpleBox applets are the following eight.  All share the one
Pure Simple entry owner `os.tools.simplebox.simplebox_main`, canonical binary
`/bin/simplebox`, and the installer-declared aliases shown below.

| Applet | Declared path | Implemented option/operand surface | Bounds |
|---|---|---|---|
| `echo` | `/bin/echo` | optional leading `-n`; remaining arguments joined by one space | output at most 65,536 bytes |
| `true` | `/bin/true` | ignores operands; returns 0 | no filesystem I/O |
| `false` | `/bin/false` | ignores operands; returns 1 | no filesystem I/O |
| `pwd` | `/bin/pwd` | no operands; currently emits `/` | rejects operands |
| `seq` | `/bin/seq` | zero operands emits nothing; otherwise parses the numeric prefix of the first operand and ignores later operands; no general GNU/POSIX range/step/format options | first operand at most 64 bytes, accepted count at most 12,773, output at most 65,536 bytes |
| `cat` | `/bin/cat` | one or more file operands; no options or stdin mode | at most 128 files, 64 MiB each, 64 KiB reads |
| `head` | `/bin/head` | optional `-n N`, then one or more files | same file/read bounds as `cat` |
| `wc` | `/bin/wc` | one or more files; always reports line, word, and byte counts | same file/read bounds as `cat` |

`/bin/busybox APPLET` is accepted by the multicall argument router, but the
installer does not declare `/bin/busybox` as a deployed alias.  It is therefore
not an installed filesystem identity.  `--list` is a SimpleBox router action,
not a ninth applet.

The image builder conditionally writes `/bin/simplebox` and declares the eight
aliases in its deployment manifest only when supplied nonempty target-native
bytes plus a matching bounded build receipt.  The current source does not
materialize those alias filesystem entries.  An empty configuration records
blocked inventory and installs no payload.  Even a staged payload remains
`filesystem-blocked`: the tracked blocker
`doc/08_tracking/bug/simpleos_primary_tool_guest_admission_identity_2026-08-22.md`
records that the booted guest cannot yet authenticate the installer admission
and mint the guest-local one-shot launch authority.  Generic and alias paths
must therefore reject before process spawn.  The typed primary-tool result uses
exit code 126; the lower-level generic launcher represents the rejection as
the internal negative result `-126`.

Target declaration is also conditional and uneven.  The installer receipt
mapper accepts `x86_64-unknown-simpleos`, `aarch64-unknown-simpleos`,
`riscv64gc-unknown-simpleos`, and `riscv32-unknown-simpleos`.  It has no i686 or
ARMv7 package-architecture row.  The current build helper admits only triples
containing or ending in `-none`, while the installer requires the four
`*-unknown-simpleos` receipt identities.  It therefore cannot by itself
produce an installer-compatible artifact; accepting a caller's freestanding
triple would not prove that an artifact exists in any case.
There is no retained FAT32, DBFS, or NVFS guest launch receipt for any target.

### Dedicated primary executables (implemented, launch blocked)

| Command | Canonical path | Pure Simple owner | Implemented surface | Current authority/runtime state |
|---|---|---|---|---|
| `sha256sum` | `/usr/bin/sha256sum` | `os.tools.shell.checksum.checksum_tool` | bounded file SHA-256 plus help/version/error behavior | no target bytes, digest, admitted receipt, or live loader token |
| `md5sum` | `/usr/bin/md5sum` | `os.tools.shell.checksum.checksum_tool` | bounded file MD5 plus help/version/error behavior | no target bytes, digest, admitted receipt, or live loader token |
| `grep` | `/usr/bin/grep` | `os.tools.shell.grep.grep_tool` | bounded line search plus help/version/error behavior | no target bytes, digest, admitted receipt, or live loader token |
| `ps` | `/usr/bin/ps` | `os.tools.proc.ps_tool` | bounded kernel task listing plus help/version/error behavior | no target bytes, digest, admitted receipt, or live loader token |

All four are `Blocked` for the six declared userland triples and all three
declared filesystems.  Those target/filesystem lists are required acceptance
scope, not availability claims.  The launcher gates direct, alias-expanded,
background, pipeline, and generic path execution; `which` may print the
canonical artifact path followed by `(artifact-gated)`, but cannot authorize
it.

### Implemented but not command-routed

`os.tools.simplebox.simplebox_applets_core` contains Pure Simple helper
logic for `dd` slicing, `timeout` duration parsing, and `chown` owner parsing.
None of `dd`, `timeout`, or `chown` appears in `simplebox_applet_names`,
`simplebox_run`, or the shell builtin set.  They are therefore
`implemented-not-dispatched`, have no installed path, options contract, target
artifact, or launch authority, and must not be advertised as SimpleBox
applets.

The primary categories `administration`, `archive/compression`, `networking`,
and `package-management` are source-declared `Blocked` in the closed manifest,
despite having no admitted executable identity.  Shell
builtins or library/service implementations with similar names do not promote
those categories: each still needs a canonical target artifact, complete
options/error contract, authenticated loader authority, and representative
FAT32/DBFS/NVFS execution receipts for every selected architecture.

## Promotion evidence checklist

For each filesystem command, retain all of the following before changing its
state: exact installed path and bytes digest; source-matched Pure Simple build
receipt; target triple; filesystem identity and generations; guest-verified
admission receipt; consumed one-shot loader authority; exact argv; bounded
stdout/stderr and exit status; one representative operation; one malformed or
I/O error path; `--help` and `--version` when claimed; and an execution receipt
for every required target/filesystem row.  A builtin run, source-level unit
case, image manifest line, QEMU fixed-command marker, or host call satisfies
none of these filesystem-launch requirements by itself.
