# Win-FS Schema

**Status:** landed in `spm-winfs-llm-suite` (2026-04-18).

## Path tree

```
/win/
  <app>/
    <wid>/
      title        # text bytes (UTF-8)
      state        # "normal" | "minimized" | "maximized" | "closed"
      geometry     # "x,y,w,h" (i32,i32,u32,u32)
      buffer       # BufferRef metadata (not the pixels; opaque handle)
      meta         # SDN key/value (app-specific)
      actions/
        close      # writing anything issues a close
        focus      # writing anything requests focus
```

`/win` is the mount point on SimpleOS. On host, the same tree is rooted at `$XDG_RUNTIME_DIR/simple-win/` (Linux), `$TMPDIR/simple-win/` (macOS), or `%LOCALAPPDATA%\simple-win\` (Windows).

## Single encoder

`src/lib/common/win_fs/fs_encoder.spl` owns encode/decode. Both the kernel VFS driver (`src/os/kernel/fs/win_vfs/win_vfs_driver.spl`) and the host shim (`src/app/simple_process_manager/winfs_shim_host.spl`) import this module. **Neither inlines encoding logic.** The AC-4 grep sentinel enforces this.

## ACL

`src/lib/common/win_fs/acl.spl`:
```
fn acl_check(rec: WindowRecord, token: AuthorityToken, op: FsOp) -> bool
```
Compares `token.id_path` against `rec.acl_id_path` via `id_path_prefix_match`, then checks `op` against `token.level` (e.g. `Read` requires `>= Internal` if the record is Internal-classed).

## Lifecycle

- Window create → `window_registry.register` → `PublishSink.publish(fs_encoder.encode_record(rec))` → kernel VFS driver on SimpleOS, host shim on others.
- Window destroy → `PublishSink.unpublish(wid)`; subsequent kernel `open()` returns `ENOENT`.
- Permission mismatch → kernel `open()` returns `EACCES`.

## Types

From `src/lib/common/win_fs/window_record.spl`:
```
class WindowRecord {
    wid: u64
    generation: u32
    app: text
    title: text
    state: WindowState         # enum { Normal, Minimized, Maximized, Closed }
    geometry: Rect             # { x: i32, y: i32, w: u32, h: u32 }
    buffer_ref: BufferRef      # { kind: text, handle: u64, bytes: u64 }
    acl_id_path: IdPath
}
```

From `src/os/kernel/types/fs_types.spl` (**corrected in wave 5b**):
```
enum FsNodeKind { File, Directory, Symlink, Device, Pipe }
class DirEntry { name: text, node: FsNode }
```

## No-duplication enforcement

- Kernel driver file: imports `lib.common.win_fs.fs_encoder` and `lib.common.win_fs.acl` only; no local `encode_*`/`decode_*`.
- Host shim file: same imports; writes `FsTree` bytes straight to the runtime dir.
- CI hint: `grep -rE '(^|[^a-z_])encode_record' src/os/kernel/fs/win_vfs/` must return zero non-import hits.
