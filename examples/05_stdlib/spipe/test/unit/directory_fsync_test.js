import test from "node:test";
import assert from "node:assert/strict";
import {
  fsyncDirectory,
  isUnsupportedDirectoryFsyncError,
  WINDOWS_UNSUPPORTED_DIRECTORY_FSYNC_CODES
} from "../../src/storage/directory_fsync.js";

function injected(code) {
  return {
    platform: "win32",
    openSync: () => 17,
    fsyncSync: () => { throw Object.assign(new Error(`injected ${code}`), { code }); },
    closeSync: () => undefined
  };
}

test("directory fsync tolerates only unsupported Windows directory errors", () => {
  assert.deepEqual(WINDOWS_UNSUPPORTED_DIRECTORY_FSYNC_CODES, ["EPERM", "EINVAL"]);
  for (const code of WINDOWS_UNSUPPORTED_DIRECTORY_FSYNC_CODES) {
    assert.equal(isUnsupportedDirectoryFsyncError({ code }, "win32"), true);
    assert.doesNotThrow(() => fsyncDirectory("ignored", injected(code)));
  }
  assert.equal(isUnsupportedDirectoryFsyncError({ code: "EPERM" }, "linux"), false);
  assert.throws(() => fsyncDirectory("ignored", { ...injected("EPERM"), platform: "linux" }), /injected EPERM/);
});

test("directory fsync propagates descriptor and unexpected Windows errors", () => {
  for (const code of ["EBADF", "EIO"]) {
    assert.equal(isUnsupportedDirectoryFsyncError({ code }, "win32"), false);
    assert.throws(() => fsyncDirectory("ignored", injected(code)), new RegExp(`injected ${code}`));
  }
});
