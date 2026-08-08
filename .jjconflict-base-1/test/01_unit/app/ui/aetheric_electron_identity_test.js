#!/usr/bin/env node
"use strict";

const assert = require("assert");
const crypto = require("crypto");
const fs = require("fs");
const os = require("os");
const path = require("path");
const { spawnSync } = require("child_process");
const {
  resolveElectronIdentity,
} = require("../../../../tools/electron-live-bitmap/aetheric_electron_identity");

const modulePath = path.resolve(
  __dirname,
  "../../../../tools/electron-live-bitmap/aetheric_electron_identity.js"
);
const root = fs.mkdtempSync(path.join(os.tmpdir(), "aetheric-electron-identity-"));
const shellRoot = path.join(root, "tools", "electron-shell");
const packageRoot = path.join(shellRoot, "node_modules", "electron");
const launcher = path.join(packageRoot, "cli.js");
const appExecutable = path.join(
  packageRoot,
  "dist",
  "Electron.app",
  "Contents",
  "MacOS",
  "Electron"
);
const installedPackage = path.join(packageRoot, "package.json");
const manifest = path.join(shellRoot, "package.json");
const lock = path.join(shellRoot, "package-lock.json");
const alternate = path.join(shellRoot, "alternate");

function writeJson(file, value) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, `${JSON.stringify(value, null, 2)}\n`);
}

function executable(file, body) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, body);
  fs.chmodSync(file, 0o755);
}

function sha256(file) {
  return crypto.createHash("sha256").update(fs.readFileSync(file)).digest("hex");
}

function resetMetadata() {
  writeJson(manifest, { dependencies: { electron: "42.5.0" } });
  writeJson(lock, {
    packages: {
      "": { dependencies: { electron: "42.5.0" } },
      "node_modules/electron": { version: "42.5.0" },
    },
  });
  writeJson(installedPackage, { version: "42.5.0" });
}

function identityOptions(overrides = {}) {
  return {
    root,
    launcher,
    appExecutable,
    package: installedPackage,
    lock,
    ...overrides,
  };
}

function reasonOf(action) {
  try {
    action();
  } catch (error) {
    return error.reason || error.message;
  }
  return "unexpected-pass";
}

function proofText(identity, overrides = {}) {
  const fields = {
    electron_launcher_path: identity.launcherPath,
    electron_launcher_sha256: identity.launcherSha256,
    electron_app_executable_path: identity.appExecutablePath,
    electron_app_executable_sha256: identity.appExecutableSha256,
    electron_package_path: identity.packagePath,
    electron_package_sha256: identity.packageSha256,
    electron_lock_path: identity.lockPath,
    electron_lock_sha256: identity.lockSha256,
    ...overrides,
  };
  return `${Object.entries(fields).map(([key, value]) => `${key}=${value}`).join("\n")}\n`;
}

function verifyProof(proof) {
  const proofPath = path.join(root, "proof.env");
  fs.writeFileSync(proofPath, proof);
  return spawnSync(
    process.execPath,
    [modulePath, "verify-proof", "--root", root, "--proof", proofPath],
    { encoding: "utf8" }
  );
}

try {
  executable(launcher, "#!/bin/sh\nexit 0\n");
  executable(appExecutable, "fixture-electron-app\n");
  executable(alternate, "alternate\n");
  resetMetadata();

  const identity = resolveElectronIdentity(identityOptions());
  assert.strictEqual(identity.version, "42.5.0");
  assert.strictEqual(identity.launcherPath, fs.realpathSync(launcher));
  assert.strictEqual(identity.appExecutablePath, fs.realpathSync(appExecutable));
  assert.strictEqual(identity.packageSha256, sha256(installedPackage));
  assert.strictEqual(identity.lockSha256, sha256(lock));

  const swappedPaths = [
    ["launcher", { launcher: alternate }, "electron-launcher-path-mismatch"],
    ["app", { appExecutable: alternate }, "electron-app-executable-path-mismatch"],
    ["package", { package: lock }, "electron-package-path-mismatch"],
    ["lock", { lock: installedPackage }, "electron-lock-path-mismatch"],
  ];
  for (const [_name, override, expectedReason] of swappedPaths) {
    assert.strictEqual(reasonOf(() => resolveElectronIdentity(identityOptions(override))), expectedReason);
  }

  const metadataCases = [
    [
      () => writeJson(manifest, { dependencies: { electron: "43.0.0" } }),
      "electron-manifest-version-mismatch",
    ],
    [
      () => writeJson(lock, {
        packages: {
          "": { dependencies: { electron: "43.0.0" } },
          "node_modules/electron": { version: "42.5.0" },
        },
      }),
      "electron-lock-root-version-mismatch",
    ],
    [
      () => writeJson(lock, {
        packages: {
          "": { dependencies: { electron: "42.5.0" } },
          "node_modules/electron": { version: "43.0.0" },
        },
      }),
      "electron-lock-installed-version-mismatch",
    ],
    [
      () => writeJson(installedPackage, { version: "43.0.0" }),
      "electron-package-version-mismatch",
    ],
  ];
  for (const [mutate, expectedReason] of metadataCases) {
    resetMetadata();
    mutate();
    assert.strictEqual(reasonOf(() => resolveElectronIdentity(identityOptions())), expectedReason);
  }
  resetMetadata();

  const validProof = verifyProof(proofText(resolveElectronIdentity(identityOptions())));
  assert.strictEqual(validProof.status, 0, validProof.stdout + validProof.stderr);
  assert.match(validProof.stdout, /aetheric_electron_identity_status=pass/);

  const hashCases = [
    "electron_launcher_sha256",
    "electron_app_executable_sha256",
    "electron_package_sha256",
    "electron_lock_sha256",
  ];
  for (const field of hashCases) {
    const result = verifyProof(proofText(identity, { [field]: "0".repeat(64) }));
    assert.strictEqual(result.status, 1);
    assert.match(result.stdout, new RegExp(`${field.replace(/_/g, "-")}-mismatch`));
  }

  const proofPathCases = [
    ["electron_launcher_path", "electron-launcher-path-mismatch"],
    ["electron_app_executable_path", "electron-app-executable-path-mismatch"],
    ["electron_package_path", "electron-package-path-mismatch"],
    ["electron_lock_path", "electron-lock-path-mismatch"],
  ];
  for (const [field, expectedReason] of proofPathCases) {
    const result = verifyProof(proofText(identity, { [field]: alternate }));
    assert.strictEqual(result.status, 1);
    assert.match(result.stdout, new RegExp(expectedReason));
  }

  for (const [mutate, expectedReason] of metadataCases) {
    resetMetadata();
    mutate();
    const result = verifyProof(proofText(identity));
    assert.strictEqual(result.status, 1);
    assert.match(result.stdout, new RegExp(expectedReason));
  }
  resetMetadata();
  process.stdout.write("aetheric-electron-identity-tests: PASS\n");
} finally {
  fs.rmSync(root, { recursive: true, force: true });
}
