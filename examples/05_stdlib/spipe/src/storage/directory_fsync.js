import { closeSync as defaultCloseSync, fsyncSync as defaultFsyncSync, lstatSync as defaultLstatSync, mkdirSync as defaultMkdirSync, openSync as defaultOpenSync, renameSync as defaultRenameSync, unlinkSync as defaultUnlinkSync, writeFileSync as defaultWriteFileSync } from "node:fs";
import { randomBytes } from "node:crypto";
import { dirname } from "node:path";

// Windows does not provide a durable directory fsync operation for every
// filesystem. These are the two unsupported-operation outcomes; descriptor
// failures such as EBADF must remain visible.
export const WINDOWS_UNSUPPORTED_DIRECTORY_FSYNC_CODES = Object.freeze(["EPERM", "EINVAL"]);

export function isUnsupportedDirectoryFsyncError(error, platform = process.platform) {
  return platform === "win32" && WINDOWS_UNSUPPORTED_DIRECTORY_FSYNC_CODES.includes(error?.code);
}

export function fsyncDirectory(path, {
  platform = process.platform,
  openSync = defaultOpenSync,
  fsyncSync = defaultFsyncSync,
  closeSync = defaultCloseSync
} = {}) {
  const descriptor = openSync(path, "r");
  try {
    try { fsyncSync(descriptor); }
    catch (error) { if (!isUnsupportedDirectoryFsyncError(error, platform)) throw error; }
  } finally {
    closeSync(descriptor);
  }
}

/**
 * Create a directory chain one component at a time. EEXIST is an expected
 * concurrent first-use outcome, but only after the winner's directory has been
 * checked as a real directory and durably observed: both the parent entry and
 * the new/observed directory are fsynced, so every ledger ancestor is on the
 * durability chain.
 */
export function mkdirDurable(path, {
  mkdirSync = defaultMkdirSync,
  lstatSync = defaultLstatSync,
  fsyncDirectory: fsyncDir = fsyncDirectory
} = {}) {
  const requireRealDirectory = (p) => {
    const observed = lstatSync(p);
    if (!observed.isDirectory() || observed.isSymbolicLink()) throw new Error("ledger ancestor is not a real directory");
  };
  const missing = [];
  let current = path;
  for (;;) {
    try { requireRealDirectory(current); break; }
    catch (error) {
      if (error?.code !== "ENOENT") throw error;
      missing.push(current);
      const parent = dirname(current);
      if (parent === current) throw new Error("ledger has no existing ancestor");
      current = parent;
    }
  }
  for (const directory of missing.reverse()) {
    try { mkdirSync(directory); }
    catch (error) { if (error?.code !== "EEXIST") throw error; }
    requireRealDirectory(directory);
    fsyncDir(dirname(directory));
    fsyncDir(directory);
  }
  requireRealDirectory(path);
  fsyncDir(dirname(path));
  fsyncDir(path);
}

/**
 * Durable atomic publish: mkdirDurable parent, unique pid+random temp, fsync
 * file, rename, fsync parent directory; temp is removed on failure.
 */
export function atomicWriteDurable(path, bytes, { mode = 0o600 } = {}) {
  mkdirDurable(dirname(path));
  const temporary = `${path}.tmp-${process.pid}-${randomBytes(8).toString("hex")}`;
  let descriptor = -1;
  try {
    descriptor = defaultOpenSync(temporary, "wx", mode);
    defaultWriteFileSync(descriptor, bytes);
    defaultFsyncSync(descriptor);
    defaultCloseSync(descriptor);
    descriptor = -1;
    defaultRenameSync(temporary, path);
  } catch (error) {
    if (descriptor !== -1) { try { defaultCloseSync(descriptor); } catch { /* original error wins */ } }
    try { defaultUnlinkSync(temporary); } catch { /* temp may already be gone */ }
    throw error;
  }
  fsyncDirectory(dirname(path));
}
