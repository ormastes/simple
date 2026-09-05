#!/usr/bin/env node
"use strict";

const crypto = require("crypto");
const fs = require("fs");
const path = require("path");

const EXPECTED_VERSION = "42.5.0";

function fail(reason) {
  const error = new Error(reason);
  error.reason = reason;
  throw error;
}

function sha256(file) {
  return crypto.createHash("sha256").update(fs.readFileSync(file)).digest("hex");
}

function readJson(file, reason) {
  try {
    return JSON.parse(fs.readFileSync(file, "utf8"));
  } catch (_error) {
    fail(reason);
  }
}

function canonicalRegularFile(file, reason) {
  let canonical;
  try {
    canonical = fs.realpathSync(file);
  } catch (_error) {
    fail(reason);
  }
  let stat;
  try {
    stat = fs.statSync(canonical);
  } catch (_error) {
    fail(reason);
  }
  if (!path.isAbsolute(canonical) || !stat.isFile()) fail(reason);
  return canonical;
}

function canonicalPlainRegularFile(file, reason) {
  let stat;
  try {
    stat = fs.lstatSync(file);
  } catch (_error) {
    fail(reason);
  }
  if (!stat.isFile() || stat.isSymbolicLink()) fail(reason);
  return canonicalRegularFile(file, reason);
}

function requirePlainDirectory(directory, reason) {
  let stat;
  try {
    stat = fs.lstatSync(directory);
  } catch (_error) {
    fail(reason);
  }
  if (!stat.isDirectory() || stat.isSymbolicLink()) fail(reason);
}

function expectedPaths(root) {
  const canonicalRoot = fs.realpathSync(root);
  const shellRoot = path.join(canonicalRoot, "tools", "electron-shell");
  const nodeModules = path.join(shellRoot, "node_modules");
  const packageRoot = path.join(nodeModules, "electron");
  requirePlainDirectory(shellRoot, "electron-shell-root-not-physical");
  requirePlainDirectory(nodeModules, "electron-node-modules-not-physical");
  requirePlainDirectory(packageRoot, "electron-package-root-not-physical");
  for (const directory of [
    path.join(packageRoot, "dist"),
    path.join(packageRoot, "dist", "Electron.app"),
    path.join(packageRoot, "dist", "Electron.app", "Contents"),
    path.join(packageRoot, "dist", "Electron.app", "Contents", "MacOS"),
  ]) {
    requirePlainDirectory(directory, "electron-app-root-not-physical");
  }
  return {
    root: canonicalRoot,
    manifest: canonicalPlainRegularFile(
      path.join(shellRoot, "package.json"),
      "electron-manifest-missing"
    ),
    launcher: canonicalPlainRegularFile(
      path.join(packageRoot, "cli.js"),
      "electron-launcher-missing"
    ),
    appExecutable: canonicalPlainRegularFile(
      path.join(packageRoot, "dist", "Electron.app", "Contents", "MacOS", "Electron"),
      "electron-app-executable-missing"
    ),
    package: canonicalPlainRegularFile(
      path.join(packageRoot, "package.json"),
      "electron-package-missing"
    ),
    lock: canonicalPlainRegularFile(
      path.join(shellRoot, "package-lock.json"),
      "electron-lock-missing"
    ),
  };
}

function resolveElectronIdentity(options) {
  const expected = expectedPaths(options.root);
  const supplied = {
    launcher: canonicalRegularFile(options.launcher, "electron-launcher-missing"),
    appExecutable: canonicalRegularFile(
      options.appExecutable,
      "electron-app-executable-missing"
    ),
    package: canonicalRegularFile(options.package, "electron-package-missing"),
    lock: canonicalRegularFile(options.lock, "electron-lock-missing"),
  };
  for (const key of ["launcher", "appExecutable", "package", "lock"]) {
    if (supplied[key] !== expected[key]) {
      const slug = key.replace(/[A-Z]/g, letter => `-${letter.toLowerCase()}`);
      fail(`electron-${slug}-path-mismatch`);
    }
  }

  const manifest = readJson(expected.manifest, "electron-manifest-invalid");
  const lock = readJson(expected.lock, "electron-lock-invalid");
  const installed = readJson(expected.package, "electron-package-invalid");
  if (!manifest.dependencies || manifest.dependencies.electron !== EXPECTED_VERSION) {
    fail("electron-manifest-version-mismatch");
  }
  if (
    !lock.packages ||
    !lock.packages[""] ||
    !lock.packages[""].dependencies ||
    lock.packages[""].dependencies.electron !== EXPECTED_VERSION
  ) {
    fail("electron-lock-root-version-mismatch");
  }
  if (
    !lock.packages["node_modules/electron"] ||
    lock.packages["node_modules/electron"].version !== EXPECTED_VERSION
  ) {
    fail("electron-lock-installed-version-mismatch");
  }
  if (installed.version !== EXPECTED_VERSION) {
    fail("electron-package-version-mismatch");
  }
  if ((fs.statSync(expected.launcher).mode & 0o111) === 0) {
    fail("electron-launcher-not-executable");
  }
  if ((fs.statSync(expected.appExecutable).mode & 0o111) === 0) {
    fail("electron-app-executable-not-executable");
  }

  return {
    version: EXPECTED_VERSION,
    launcherPath: expected.launcher,
    launcherSha256: sha256(expected.launcher),
    appExecutablePath: expected.appExecutable,
    appExecutableSha256: sha256(expected.appExecutable),
    packagePath: expected.package,
    packageSha256: sha256(expected.package),
    lockPath: expected.lock,
    lockSha256: sha256(expected.lock),
  };
}

function readProof(file) {
  const proof = {};
  for (const line of fs.readFileSync(file, "utf8").split(/\r?\n/)) {
    if (!line) continue;
    const split = line.indexOf("=");
    if (split <= 0) fail("electron-proof-invalid");
    const key = line.slice(0, split);
    if (Object.prototype.hasOwnProperty.call(proof, key)) fail("electron-proof-invalid");
    proof[key] = line.slice(split + 1);
  }
  return proof;
}

function verifyProofIdentity(root, proof) {
  const identity = resolveElectronIdentity({
    root,
    launcher: proof.electron_launcher_path,
    appExecutable: proof.electron_app_executable_path,
    package: proof.electron_package_path,
    lock: proof.electron_lock_path,
  });
  const checks = [
    ["electron_launcher_sha256", identity.launcherSha256, "electron-launcher-sha256-mismatch"],
    [
      "electron_app_executable_sha256",
      identity.appExecutableSha256,
      "electron-app-executable-sha256-mismatch",
    ],
    ["electron_package_sha256", identity.packageSha256, "electron-package-sha256-mismatch"],
    ["electron_lock_sha256", identity.lockSha256, "electron-lock-sha256-mismatch"],
  ];
  for (const [field, expected, reason] of checks) {
    if (proof[field] !== expected) fail(reason);
  }
  return identity;
}

function option(name) {
  const index = process.argv.indexOf(name);
  return index >= 0 ? String(process.argv[index + 1] || "") : "";
}

function main() {
  if (process.argv[2] !== "verify-proof") fail("usage-verify-proof");
  const root = option("--root");
  const proofPath = option("--proof");
  if (!root || !proofPath) fail("usage-verify-proof");
  verifyProofIdentity(root, readProof(proofPath));
  process.stdout.write("aetheric_electron_identity_status=pass\n");
  process.stdout.write("aetheric_electron_identity_reason=pass\n");
}

if (require.main === module) {
  try {
    main();
  } catch (error) {
    const reason = error && error.reason ? error.reason : "electron-identity-validation-failed";
    process.stdout.write("aetheric_electron_identity_status=fail\n");
    process.stdout.write(`aetheric_electron_identity_reason=${reason}\n`);
    process.exit(1);
  }
}

module.exports = {
  EXPECTED_VERSION,
  resolveElectronIdentity,
  verifyProofIdentity,
};
