import { existsSync, mkdirSync, openSync, closeSync, fsyncSync, readFileSync, renameSync, unlinkSync, writeFileSync } from "node:fs";
import { dirname } from "node:path";

import { canonicalJson, freezeDeep, sha256Hex } from "./canonical.js";

const STORES = new WeakSet();
function validPolicy(value) {
  if (!value || typeof value !== "object" || Array.isArray(value)) return false;
  const expected = ["keys", "policyVersion", "revocationEpoch", "revokedReceiptUids"];
  const actual = Object.keys(value).sort();
  if (actual.length !== expected.length || actual.some((key, index) => key !== expected[index])) return false;
  if (typeof value.policyVersion !== "string" || !Number.isSafeInteger(value.revocationEpoch) || value.revocationEpoch < 0 ||
      !Array.isArray(value.keys) || !Array.isArray(value.revokedReceiptUids)) return false;
  const seen = new Set();
  return value.keys.every((key) => {
    const names = ["algorithm", "authorityKeyId", "epoch", "issuerKeyId", "status"];
    return key && typeof key === "object" && Object.keys(key).sort().every((name, i) => name === names[i]) &&
      names.length === Object.keys(key).length && typeof key.authorityKeyId === "string" && typeof key.issuerKeyId === "string" &&
      key.algorithm === "ed25519" && Number.isSafeInteger(key.epoch) && key.epoch >= 0 && key.status === "current" && !seen.has(key.authorityKeyId) && (seen.add(key.authorityKeyId), true);
  }) && value.revokedReceiptUids.every((id) => typeof id === "string");
}
function record(policy) {
  if (!validPolicy(policy)) throw new TypeError("read receipt policy is invalid");
  const canonical = JSON.parse(canonicalJson(policy));
  return freezeDeep({ policy: canonical, digest: sha256Hex(canonicalJson(canonical)) });
}
function bytes(policy) { return `${canonicalJson(record(policy))}\n`; }
function durableWrite(path, value) {
  const fd = openSync(path, "wx");
  try { writeFileSync(fd, value, { encoding: "utf8" }); fsyncSync(fd); } finally { closeSync(fd); }
}
function monotonic(current, next) {
  if (next.revocationEpoch < current.revocationEpoch) return false;
  const revoked = new Set(next.revokedReceiptUids);
  if (!current.revokedReceiptUids.every((id) => revoked.has(id))) return false;
  const nextKeys = new Map(next.keys.map((key) => [key.authorityKeyId, key]));
  return current.keys.every((key) => nextKeys.has(key.authorityKeyId) && nextKeys.get(key.authorityKeyId).epoch >= key.epoch);
}

/** Durable, lock/CAS protected current issuer/key/epoch/revocation policy. */
export class ReadReceiptPolicyStore {
  constructor({ path, initialPolicy = null } = {}) {
    if (typeof path !== "string" || path.length === 0) throw new TypeError("policy path is required");
    this.path = path; this.lockPath = `${path}.lock`;
    mkdirSync(dirname(path), { recursive: true });
    if (!existsSync(path)) {
      if (initialPolicy === null) throw new TypeError("initial policy is required");
      durableWrite(path, bytes(initialPolicy));
    }
    this.read(); STORES.add(this);
  }
  read() {
    const value = JSON.parse(readFileSync(this.path, "utf8"));
    if (!value || typeof value !== "object" || Object.keys(value).sort().join(",") !== "digest,policy") throw new Error("read receipt policy record is malformed");
    const rebuilt = record(value.policy);
    if (rebuilt.digest !== value.digest || canonicalJson(rebuilt) !== canonicalJson(value)) throw new Error("read receipt policy record failed verification");
    return rebuilt;
  }
  compareAndSwap(expectedDigest, nextPolicy) {
    let lock = null, ownsLock = false;
    try {
      lock = openSync(this.lockPath, "wx"); ownsLock = true;
      const current = this.read();
      if (current.digest !== expectedDigest) return null;
      if (!monotonic(current.policy, nextPolicy)) return null;
      const next = record(nextPolicy), temporary = `${this.path}.tmp-${process.pid}-${Date.now()}`;
      durableWrite(temporary, `${canonicalJson(next)}\n`);
      renameSync(temporary, this.path);
      const directory = openSync(dirname(this.path), "r"); try { fsyncSync(directory); } finally { closeSync(directory); }
      return next;
    } catch (error) {
      if (error?.code === "EEXIST") return null;
      throw error;
    } finally {
      if (lock !== null) closeSync(lock);
      if (ownsLock) try { unlinkSync(this.lockPath); } catch (error) { if (error?.code !== "ENOENT") throw error; }
    }
  }
}
export function createReadReceiptPolicyStore(options) { return new ReadReceiptPolicyStore(options); }
export function isReadReceiptPolicyStore(value) { return STORES.has(value); }
