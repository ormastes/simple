import { sign, verify } from "node:crypto";
import { canonicalJson, freezeDeep, sha256Hex } from "../storage/canonical.js";
import { SnapshotAuthorityPortV1 } from "./authority.js";

const PROJECTION_PORTS = new WeakSet();
const CURSOR_AUTHORITIES = new WeakSet();
const fail = () => Object.freeze({ ok: false, error: "SPK-W5A-DENIED" });
const ok = (value) => Object.freeze({ ok: true, value });
const hash = (value) => sha256Hex(canonicalJson(value));
const compare = (a, b) => a < b ? -1 : a > b ? 1 : 0;
function pageLimit(value) { if (!Number.isSafeInteger(value) || value < 1 || value > 100) throw new TypeError("page limit is invalid"); return value; }
function cursorBinding(view, directory, order, page, position) { return freezeDeep({ version: 1, authoritySnapshotUid: view.authoritySnapshotUid, authorityEpoch: "0", workspaceUid: view.binding.workspaceUid, projectUidOrNull: view.binding.projectUidOrNull, worktreeUid: view.binding.worktreeUid, snapshotUid: view.binding.snapshotUid, revisionId: view.binding.revisionId, viewKind: directory.viewKind, effectiveScopeDigest: directory.selectorDigest, selectorDigest: directory.selectorDigest, normalizedLogicalPath: directory.logicalPath, orderingVersion: order, pageLimit: page, lastSortKey: position, manifestDigest: view.manifestDigest }); }
function payload(binding, issuerKeyId, issuedAtMs, expiresAtMs, revocationEpoch) { return { binding, ...binding, issuerKeyId, issuedAtMs, expiresAtMs, revocationEpoch, receiptUid: `C-${hash({ binding, issuerKeyId, issuedAtMs, expiresAtMs, revocationEpoch }).slice(0, 32).toUpperCase()}` }; }

/** Composition-root signer/verifier for portable CursorReceiptV1 records. */
export class CursorAuthorityV1 {
  #issuer; #private; #keys; #now; #epoch; #revoked;
  constructor({ issuerKeyId, privateKey = null, publicKeys, now = () => Date.now(), revocationEpoch = "0", revokedReceiptUids = [] }) { if (typeof issuerKeyId !== "string" || !issuerKeyId || !publicKeys || typeof publicKeys !== "object") throw new TypeError("CursorAuthorityV1 requires issuer and public keys"); this.#issuer = issuerKeyId; this.#private = privateKey; this.#keys = new Map(Object.entries(publicKeys)); this.#now = now; this.#epoch = String(revocationEpoch); this.#revoked = new Set(revokedReceiptUids); if (!this.#keys.has(issuerKeyId)) throw new TypeError("cursor issuer key is unavailable"); CURSOR_AUTHORITIES.add(this); }
  issue(binding, ttlMs = 60_000) { if (!this.#private || !Number.isSafeInteger(ttlMs) || ttlMs < 1) throw new TypeError("CursorAuthorityV1 cannot sign cursor"); const issuedAtMs = this.#now(); const value = payload(binding, this.#issuer, issuedAtMs, issuedAtMs + ttlMs, this.#epoch); return freezeDeep({ ...value, signature: sign(null, Buffer.from(canonicalJson(value)), this.#private).toString("base64") }); }
  verify(cursor, expected) { try { if (!cursor || typeof cursor !== "object" || this.#revoked.has(cursor.receiptUid)) return null; const value = payload(cursor.binding, cursor.issuerKeyId, cursor.issuedAtMs, cursor.expiresAtMs, cursor.revocationEpoch); if (canonicalJson(value) !== canonicalJson({ ...cursor, signature: undefined }) || cursor.revocationEpoch !== this.#epoch || value.issuedAtMs > this.#now() || value.expiresAtMs <= this.#now()) return null; const key = this.#keys.get(value.issuerKeyId); if (!key || !verify(null, Buffer.from(canonicalJson(value)), key, Buffer.from(cursor.signature, "base64"))) return null; return canonicalJson(value.binding) === canonicalJson(expected) ? freezeDeep(value) : null; } catch { return null; } }
}

export class ProjectionPortV1 {
  #authority; #cursorAuthority;
  constructor({ authority, cursorAuthority }) { if (!(authority instanceof SnapshotAuthorityPortV1) || !(cursorAuthority instanceof CursorAuthorityV1)) throw new TypeError("ProjectionPortV1 requires SnapshotAuthorityPortV1 and CursorAuthorityV1"); this.#authority = authority; this.#cursorAuthority = cursorAuthority; PROJECTION_PORTS.add(this); }
  render(view, target) { if (!this.#authority.isTarget(target)) return fail(); const record = this.#authority.recordFor(view); if (!record || canonicalJson(target.binding) !== canonicalJson(view.binding) || target.manifestDigest !== view.manifestDigest) return fail(); const found = record.inventory.entries.find((item) => item.targetKind === target.targetKind && item.targetUid === target.targetUid); return found ? ok(Object.freeze({ targetKind: found.targetKind, targetUid: found.targetUid, logicalPath: found.logicalPath, bytes: Buffer.from(found.content, "utf8"), contentDigest: sha256Hex(found.content), manifestDigest: view.manifestDigest })) : fail(); }
  list(view, directory, request = {}) {
    if (!this.#authority.isDirectory(directory)) return fail(); const record = this.#authority.recordFor(view); if (!record || canonicalJson(directory.binding) !== canonicalJson(view.binding) || directory.manifestDigest !== view.manifestDigest) return fail();
    try { const limit = pageLimit(request.limit ?? 100); const order = request.orderingVersion ?? "spipe-directory-v1"; if (order !== "spipe-directory-v1") return fail(); let after = "";
      if (request.cursor !== undefined && request.cursor !== null) { const verified = this.#cursorAuthority.verify(request.cursor, cursorBinding(view, directory, order, limit, request.cursor.binding?.lastSortKey)); if (!verified) return fail(); after = verified.lastSortKey; }
      const all = record.inventory.entries.filter((item) => item.directoryPath === directory.logicalPath).map((item) => ({ ...item, pageSortKey: `${item.title.normalize("NFC")}\0${item.targetKind}\0${item.targetUid}` })).sort((a, b) => compare(a.pageSortKey, b.pageSortKey));
      const entries = all.filter((item) => compare(item.pageSortKey, after) > 0).slice(0, limit).map((item) => freezeDeep({ targetKind: item.targetKind, targetUid: item.targetUid, logicalPath: item.logicalPath, title: item.title, sortKey: item.pageSortKey, manifestDigest: view.manifestDigest }));
      const more = all.some((item) => compare(item.pageSortKey, entries.at(-1)?.sortKey ?? after) > 0); const cursor = more && entries.length ? this.#cursorAuthority.issue(cursorBinding(view, directory, order, limit, entries.at(-1).sortKey)) : null;
      return ok(freezeDeep({ entries, cursor, manifestDigest: view.manifestDigest, orderingVersion: order }));
    } catch { return fail(); }
  }
}
export function isProjectionPortV1(value) { return PROJECTION_PORTS.has(value); }
