# SimpleOS primary tool manifest

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
| administration | no admitted executable | `Unavailable` |
| archive/compression | no admitted executable | `Unavailable` |
| networking | no admitted executable | `Unavailable` |
| checksums | `/usr/bin/sha256sum`, `/usr/bin/md5sum` | `Blocked` |
| text processing | `/usr/bin/grep` | `Blocked` |
| process monitoring | `/usr/bin/ps` | `Blocked` |
| package management | no admitted executable | `Unavailable` |

The three blocked categories have real pure-Simple owners and bounded behavior:
checksum and grep read through `VfsManager.read_bytes_bounded` with a 64 MiB
per-file limit, 64 KiB chunks, and at most 128 files; `ps` consumes the one
`list_tasks` owner, capped at 256 tasks and 32 command arguments. Their package
identities intentionally carry empty artifact-digest and admission-receipt
fields. The launcher returns exit 126 and `loader_authority_state=absent` for
these known files, or 127 for an unknown identity. It never treats that text
state as an executable-authority token and never falls back to an in-process
shortcut, PATH lookup, alias expansion, background execution, or pipeline
execution. The generic `launcher_launch_path_with_args` boundary also rejects
all four canonical paths before process spawn, so async and non-shell launcher
callers cannot bypass the tool-specific gates.

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

`simplebox_inventory_applet_names_v1` is the authoritative closed inventory of
41 routed applets. Every row below enters through the Pure Simple source
`src/os/tools/simplebox/simplebox_main.spl` (`main` -> `simplebox_run`) and maps
its declared alias to the canonical artifact `/bin/simplebox` through
`simplebox_resolve_canonical_path_v1`. The production launcher caller
`launcher_launch_path_with_args` currently stops each identity at
`primary_tool_path_requires_loader_authority_v1`, before
`_launcher_spawn_under_recipe`. Thus “declared path” is installer/catalog
metadata, not proof that the path exists in a booted filesystem.

| Tool | Declared filesystem path | Pure Simple entrypoint | Production caller/evidence | Status |
|---|---|---|---|---|
| `echo` | `/bin/echo` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `printf` | `/bin/printf` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `true` | `/bin/true` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `false` | `/bin/false` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `pwd` | `/bin/pwd` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `seq` | `/bin/seq` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `sleep` | `/bin/sleep` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `cat` | `/bin/cat` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `head` | `/bin/head` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `tail` | `/bin/tail` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `wc` | `/bin/wc` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `tee` | `/bin/tee` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `cp` | `/bin/cp` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `mv` | `/bin/mv` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `ls` | `/bin/ls` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `mkdir` | `/bin/mkdir` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `rm` | `/bin/rm` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `rmdir` | `/bin/rmdir` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `chmod` | `/bin/chmod` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `touch` | `/bin/touch` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `ln` | `/bin/ln` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `basename` | `/bin/basename` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `dirname` | `/bin/dirname` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `readlink` | `/bin/readlink` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `which` | `/bin/which` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `stat` | `/bin/stat` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `find` | `/bin/find` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `grep` | `/bin/grep` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `sort` | `/bin/sort` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `sed` | `/bin/sed` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `uniq` | `/bin/uniq` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `cut` | `/bin/cut` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `tr` | `/bin/tr` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `cmp` | `/bin/cmp` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `od` | `/bin/od` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `strings` | `/bin/strings` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `file` | `/bin/file` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `comm` | `/bin/comm` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `paste` | `/bin/paste` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `nl` | `/bin/nl` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |
| `join` | `/bin/join` | `simplebox_main.main` | generic launcher rejects without loader authority | `filesystem-blocked` |

The same catalog contract declares `/bin/busybox` as a multicall alias for
`/bin/simplebox`; it is not a separate tool or payload. `--list` is a router
action, not a 42nd applet.

The image builder conditionally writes `/bin/simplebox` and declares all 42
aliases (`/bin/busybox` plus the 41 applet paths) only when supplied nonempty
target-native bytes plus its validated build receipt. The alias records are
manifest declarations; `_stage_simplebox_payload` does not create alias files.
An empty configuration records blocked inventory and installs no payload, and
signed catalog admission remains a separate launch requirement. Even a staged
payload remains `filesystem-blocked`: the tracked blocker
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

### Combined Clang + primary catalog boot (2026-08-25, unverified)

The current implementation under review no longer asks the primary-tool lane
to seal its five rows independently. It authenticates the nine-record
Clang/sysroot release and five-record primary release under one shared release
identity, gives the primary plan sole ownership of `/bin/simplebox`, and then
requests one fourteen-record catalog population. The x86_64, ARM64, and RV64
adapters delegate to that shared owner.

This is not launch evidence. `ImageBuilder._materialize_primary_artifact`
still creates a real disk only for the non-installer x86_64 FAT32 route;
descriptor fallback and DBFS/NVFS selection metadata do not prove that signed
payloads exist in a boot-mounted filesystem. Promotion still requires fresh
per-ISA/per-filesystem receipts described in
`doc/03_plan/agent_tasks/simpleos_combined_signed_catalog_boot.md`. The i686,
ARMv7, and RV32 rows remain blocked on complete target sysroots and native
payloads; a 64-bit catalog receipt cannot promote them.

### Dedicated primary executables (implemented, launch blocked)

| Command | Canonical path | Pure Simple entrypoint | Production caller/evidence | Status |
|---|---|---|---|---|
| `sha256sum` | `/usr/bin/sha256sum` | `src/os/apps/coreutils/entries/sha256sum_main.spl` (`main`) | shell `launcher_dispatch_checksum_tool_v1`; generic launcher also rejects before spawn; no admitted target receipt/token | `filesystem-blocked` |
| `md5sum` | `/usr/bin/md5sum` | `src/os/apps/coreutils/entries/md5sum_main.spl` (`main`) | shell `launcher_dispatch_checksum_tool_v1`; generic launcher also rejects before spawn; no admitted target receipt/token | `filesystem-blocked` |
| `grep` | `/usr/bin/grep` | `src/os/apps/coreutils/entries/grep_main.spl` (`main`) | shell `launcher_dispatch_text_tool_v1`; generic launcher also rejects before spawn; no admitted target receipt/token | `filesystem-blocked` |
| `ps` | `/usr/bin/ps` | `src/os/apps/coreutils/entries/ps_main.spl` (`main`) | shell `launcher_dispatch_process_tool_v1`; generic launcher also rejects before spawn; no admitted target receipt/token | `filesystem-blocked` |

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
