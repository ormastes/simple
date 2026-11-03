import { closeSync as defaultCloseSync, fsyncSync as defaultFsyncSync, lstatSync as defaultLstatSync, mkdirSync as defaultMkdirSync, openSync as defaultOpenSync } from "node:fs";
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
