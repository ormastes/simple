# Shared-cache directory roots v1

Status: native C owner verified on Windows and Linux. The first generated
Simple attempt failed in the diagnostic compiler's imported library MIR before
producing an executable. Its ABI, frontend reuse and deployment remain unverified.

The existing shared-cache REQ-004 and REQ-007 require the immutable parse-cell
root to be physically separate from mutable frontend state. An absolute path
string cannot establish this: Windows SUBST and Linux bind mounts can expose
the same directory through distinct paths.

`std.nogc_sync_mut.io.directory_roots_v1` owns the native boundary;
`std.nogc_async_mut.sosix.directory_roots_v1` re-exports that owner. Compiler
callers use a stateless facade. No mutable Simple token state crosses compiler
workers. The native mutex owns a bounded 32-entry admission memo and 32 token
slots. Failure is sticky for a requested root pair within the process. Token
generations never reuse a closed identity; exhaustion fails closed.

Paths cross the ABI as bounded byte arrays, not unregistered text pointer/length
pairs. Native array validation rejects embedded NUL and oversized input before
copying. Identity output is exactly eight 64-bit words and reuses
`DescriptorFileIdentityV1`; caller-owned output memory is released on both paths.
The compiled fixture must validate this ABI separately from the C selfcheck.

Windows opens every directory ancestor without DELETE sharing and with
FILE_LIST_DIRECTORY plus FILE_READ_ATTRIBUTES. It rejects reparse nodes and
uses volume/file identity and a normalized volume-GUID handle path. Actual tests
showed FILE_READ_ATTRIBUTES alone did not block rename; the final access mask
is verified against both root and ancestor renames. SUBST aliases resolve to
the same physical location. See Microsoft's
[handle-path contract](https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-getfinalpathnamebyhandlew).

Linux opens each component with openat/O_NOFOLLOW and keeps the final fd.
Device/inode, fdinfo mount ID and mountinfo filesystem root establish physical
ancestry. Visible lexical nesting is additionally rejected across separate
child filesystems. Every validation resolves the current mount-root relation:
a bind mount's backing directory can move underneath the shared root while its
inode and mount ID remain unchanged. See the kernel's
[proc filesystem documentation](https://cdn.kernel.org/doc/html/latest/filesystems/proc.html).

The shared directory must already exist. A missing private subtree is created
only after its nearest existing no-follow parent and prospective physical path
pass the separation check. Linux walks mkdirat/openat relative to an owned fd;
Windows retains ancestor handles while creating/opening each component. A
concurrent creator's EEXIST is reopened and validated, never blindly accepted.
No forbidden nested subtree is created just to discover that it overlaps.

Both frontend private-cache enablement and shared-cell key admission call the
guard. A renamed or remounted root fails before the next cache operation. This
is an admission/revalidation contract, **not an anchored write transaction**:
existing pathname-based cache I/O remains subject to a change between validation
and I/O. Deployment requires owner-controlled ancestors; hostile concurrent
filesystem mutation needs descriptor-relative cell/private-cache I/O before a
stronger guarantee can be claimed.

Native checks hold a process mutex across filesystem validation. On this host,
256 warm checks used 106.133 ms CPU on WSL D: (about 0.415 ms/check) and 29 ms
on native Windows D: (about 0.113 ms/check). These are diagnostic samples, not
end-to-end cache speedup evidence. Linux's earlier inode/mount-ID shortcut
measured 87.943 ms but was rejected for correctness. Full frontend warm/cold
comparison and realistic throughput remain release gates.

Ownership: shared-cache Astra owns this capsule and integration; the existing
shared-cache deployment reviewer reviews it independently. No extra sidecar
lane or production host writer is introduced.
