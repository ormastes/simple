# Retained cgroup removal and terminal population evidence

Status: **SOURCE RESEARCH ONLY — terminal proof not admitted**. No native code,
ABI, test run or Host discharge rule changes in this checkpoint. The existing
observer continues to return uncertainty for inaccessible or removed subjects.

## Result

Linux v6.12 establishes a useful kernel invariant: successful removal of an
already live non-root cgroup requires no live population and no online child
cgroups, and disables future entry into that same cgroup before removing its
files. A descriptor retained from capture keeps the old native object distinct
from any later same-path object.

Userspace still needs a qualified observation of that transition. A retained
directory FD, a missing pathname, zero CLI exit, empty engine database, directory
link count, or generic ENODEV is insufficient. A narrowly qualified fresh read
of the exact previously active core `cgroup.events` FD is a candidate, but the
current installed profiles do not prove the running kernel implementation or
syscall provenance required to promote that candidate into terminal evidence.

This resolves the source-level ordering question and identifies an implementable
qualification boundary. It does **not** establish physical containment or authorize
capacity release.

## Immutable primary sources

All source findings below refer to Linux v6.12 commit
`adc218676eef25575469234709c2d87185ca223a` (not current main).
Exact Git blob identities are in
`linux_cgroup_terminal_observation_sources_v1.sdn`.
Files were obtained through the GitHub source connector; no kernel was built or
executed. Version 6.12 is a studied implementation, not an assertion about the
running host kernel. Vendor patches/configuration and later versions require
their own qualification.

| Question | Pinned source and conclusion |
|---|---|
| Population and descendants | [cgroup_destroy_locked](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/cgroup/cgroup.c#L5965) checks population and online children while holding cgroup_mutex. Population includes direct populated css_sets plus populated domain/threaded children: [definition](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/include/linux/cgroup.h#L556). |
| No entry after removal begins | The same destroy function clears CSS_ONLINE before core-file removal. [cgroup_kn_lock_live](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/cgroup/cgroup.c#L1640) refuses dead groups; [procs/threads write](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/cgroup/cgroup.c#L5190) uses that gate. [CLONE_INTO_CGROUP](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/cgroup/cgroup.c#L6472) separately rejects a dead destination under cgroup_mutex. |
| Child creation | [cgroup_mkdir](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/cgroup/cgroup.c#L5811) gates the parent through cgroup_kn_lock_live. Creation is activated only after files/controllers are populated; failed construction is not a previously successful capture. |
| Retained directory stat | [kernfs_refresh_inode/getattr](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/fs/kernfs/inode.c#L167) refreshes directory nlink from subdirs + 2. An open removed cgroup directory therefore does not have a general nlink==0 removal contract. Device/inode still identify the pin; they do not reveal dead state. |
| Kernfs removal | [__kernfs_remove](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/fs/kernfs/dir.c#L1447) marks/deactivates and drains nodes before unlinking them. [activation](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/fs/kernfs/dir.c#L1370) does not revive a removing node. |
| Fresh events read | [kernfs_seq_start](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/fs/kernfs/file.c#L145) obtains an active reference or returns ENODEV. [seq_read_iter](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/fs/seq_file.c#L171) resets cached records for a zero-offset read. [cgroup_events_show](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/cgroup/cgroup.c#L3666) reports population/frozen state and returns success. |
| Generic notifications | [kernfs poll](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/fs/kernfs/file.c#L836) uses the same error/priority flags for ordinary change notifications and inactive nodes. Poll flags alone cannot distinguish deletion. |
| Hiding versus removal | [kernfs_show](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/fs/kernfs/dir.c#L1409) can temporarily deactivate files. Therefore an arbitrary kernfs file's ENODEV is not terminal proof. The studied cgroup.c hides PSI files, not the core events file; full configured-kernel callsite qualification remains required. |
| Core events removal | [css_clear_dir](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/cgroup/cgroup.c#L1695) removes base files for the self CSS. Published non-root destruction reaches it after marking dead. [creation rollback](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/cgroup/cgroup.c#L1728) also removes base files before activation, so the candidate must require successful live capture and a validated events read. |
| Mount disappearance | [cgroup_kill_sb](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/cgroup/cgroup.c#L2305) does not destroy the default hierarchy root merely because its mount disappears. An inaccessible mount is not workload emptiness. |
| Errno provenance | [seccomp ERRNO action](https://github.com/torvalds/linux/blob/adc218676eef25575469234709c2d87185ca223a/kernel/seccomp.c#L1240) can synthesize an errno while skipping the syscall. Generic ENODEV is not sufficient even when the application holds the right FD. |

## Candidate A: exact core-events deactivation

This is a conditional inference from the pinned source, not a supported current
receipt. If a known active non-root cgroup's **same pinned core events object**
becomes permanently inactive through the qualified removal path, the kernel has
already checked zero population, excluded online children and marked the cgroup
dead. The original object then cannot receive new tasks or children. Same-name
recreation creates a different object and cannot repopulate that retained pin.

A bounded implementation proposal uses the existing registry owner, with a
distinct versioned terminal-observation operation only after these prerequisites:

1. An installed, authenticated kernel qualification profile binds actual running
   kernel build identity, approved source/configuration/patch manifest and this
   precise cgroup/kernfs/seq-file behavior. Bare uname text or an arbitrary
   caller-provided source hash is not qualification.
2. Capture pins exact cgroup and core-events FD identities/mount, namespaces and
   provider association. It requires a valid fresh events read while the primary
   is associated and alive. Current capture alone only opens the events FD
   before the facade's subsequent observe; the stronger baseline needs an
   explicit native retained successful-read state.
3. The Host retains a same-journal teardown fence preventing new child
   admission/start/resume for that runtime identity. The provider binds the
   separately authorized lifecycle operation and its result to the owner.
4. The terminal operation validates origin, namespaces, mount and original FD
   identity without reopening a path or demanding that the removed pathname
   still resolve. It performs one bounded zero-offset read on the retained core
   events FD. Positive data remains a populated/empty snapshot. Other errors,
   partial data, missing baseline, changed mount and identity mismatch remain
   unknown.
5. ENODEV can be considered a candidate only under the qualified call-path and
   trusted-syscall execution profile. At minimum unqualified seccomp/notification,
   ptrace/interposition and custom kernel paths cannot silently inherit this
   inference. The active kernel build and host process protection assumptions
   must be explicit and independently enforced/qualified, not a request bool.
6. Any terminal fact binds the old native cgroup/events identity, capture and
   lifecycle association, kernel-profile digest and observation time. It does
   not relabel an ENOENT pathname result, does not adopt a new path occupant,
   does not close the observation owner and does not itself commit release.

The current V1 ABI stays unchanged. No terminal enum/receipt is added on the
strength of this design alone. Implementation requires the kernel/profile and
syscall provenance producer plus independent source review and actual native
acceptance. A complete configured-kernel removal/hide callsite audit is still
open; the bounded core study above is not an all-modules proof.

Even a valid terminal cgroup fact is insufficient if a workload could migrate
outside the group earlier. The provider's creation-time confinement profile and
no-escape guarantees are separate mandatory evidence. A dead empty group cannot
prove the exit of an escaped descendant.

## Candidate B: pre-removal empty barrier

If Candidate A cannot be qualified, the provider needs an explicit two-phase
runtime contract:

- Host durably fences new child admission/start/resume, then stops workload
  activity through the authorized lifecycle path.
- The selected OCI runtime keeps the exact cgroup alive and readable until the
  retained native owner observes it empty. The runtime must not remove the
  directory before this handshake.
- Actual enforced writer/delegation policy excludes external migration,
  CLONE_INTO_CGROUP and same-scope recreation between that observation and
  removal. A journal mutex alone does not constrain independent cgroup writers.
- The owner archives the exact empty observation and fence evidence; the runtime
  then removes that same group under the qualified exclusive identity/namespace
  protocol and returns its exact correlated completion.
- Host archives the terminal evidence and records parent removed / child outcome
  unknown. Workload cleanup, helper cleanup and storage retirement remain
  separate conditions before capacity release.

No such retain-before-delete runtime port is currently present or qualified.
The installed Podman profile selects an operator-provided runtime executable and
digest, but no concrete runtime version/fixture is selected in this environment.
Podman 5.2.5 cleanup delegates OCI deletion and may remove its own database state
despite cleanup errors. Thus current provider absence cannot implement this
protocol. A path-stat followed by rmdir is also not an atomic exact-object delete;
same-path replacement must be excluded by actual enforced authority.

## Required physical acceptance

All cases are **NOT_RUN**; no privileged setup or native campaign is authorized
by this document.

- A live descendant keeps population true after its direct exec/helper exits.
  Removal while populated or with an online child fails and cannot yield a
  terminal receipt.
- Successful actual removal follows an observed exact live capture, including
  the runtime's real deletion ordering. Fresh retained events reads, inode
  identity and namespace/mount facts are recorded without substituting a model.
- Same-path recreation, ancestor/mount replacement and detached mounts never
  rebind the old owner or turn generic errors into terminal proof.
- Ordinary events notifications, partial/cached reads, EIO/EACCES/EBADF/ENOENT,
  hidden unrelated files and injected seccomp ENODEV all remain unknown.
- The pinned group cannot be repopulated after the qualified terminal transition;
  actual migration, clone-into-group and child creation adversaries are refused.
- No earlier migration outside the scope is possible under the creation profile.
- Crash/restart without recoverable qualified native identity and archived proof
  keeps the charge. A proof archives unknown child outcome, never successful exit.

The immediate next implementation work is the installed kernel/runtime
qualification and same-journal fence producer, or an explicitly selected runtime
retain/delete handshake. Extending the observer to manufacture a terminal flag
from current errors would weaken the outstanding gate and is rejected.

