import { closeSync as defaultCloseSync, fsyncSync as defaultFsyncSync, openSync as defaultOpenSync } from "node:fs";

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
