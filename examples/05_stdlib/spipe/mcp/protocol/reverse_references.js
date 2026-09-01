import { randomBytes } from "node:crypto";
import { closeSync, constants, fstatSync, openSync, readFileSync } from "node:fs";
import { resolve } from "node:path";

import { createFolderReverseReferenceIndex } from "../../src/graph/index.js";

const MAX_INVENTORY_BYTES = 64 * 1024 * 1024;
const MAX_CACHE_ENTRIES = 8;

function inventoryFingerprint(stat) {
  return `${stat.dev}:${stat.ino}:${stat.size}:${stat.mtimeMs}:${stat.ctimeMs}`;
}

// ctime is cache-relevant metadata, but not byte identity: renaming an already
// opened inode changes ctime without changing the descriptor's content.
function inventoryByteIdentity(stat) {
  return `${stat.dev}:${stat.ino}:${stat.size}:${stat.mtimeMs}`;
}

function assertRegularInventory(stat) {
  if (!stat.isFile() || stat.isSymbolicLink()) {
    throw new TypeError("inventory_path must name a regular file, not a symbolic link");
  }
  if (stat.size > MAX_INVENTORY_BYTES) {
    throw new RangeError(`compiled inventory exceeds ${MAX_INVENTORY_BYTES} bytes`);
  }
}

function openNoFollow(path) {
  if (typeof constants.O_NOFOLLOW !== "number") {
    throw new Error("secure no-follow inventory opening is unavailable on this host");
  }
  try { return openSync(path, constants.O_RDONLY | constants.O_NOFOLLOW); }
  catch (error) {
    if (error?.code === "ELOOP") throw new TypeError("inventory_path must name a regular file, not a symbolic link");
    throw error;
  }
}

function readOpenedInventory(fd, stat) {
  const bytes = readFileSync(fd);
  if (bytes.length > MAX_INVENTORY_BYTES) {
    throw new RangeError(`compiled inventory exceeds ${MAX_INVENTORY_BYTES} bytes`);
  }
  const after = fstatSync(fd);
  if (inventoryByteIdentity(after) !== inventoryByteIdentity(stat)) {
    throw new Error("compiled inventory changed while it was being read");
  }
  let inventory;
  try { inventory = JSON.parse(bytes.toString("utf8")); }
  catch { throw new TypeError("compiled inventory must be valid JSON"); }
  return { inventory, fingerprint: inventoryFingerprint(after) };
}

/**
 * Request adapter over immutable compiler inventories.
 *
 * The small LRU avoids rebuilding the reverse index on every MCP request. A
 * file identity/size/mtime change invalidates the cached entry before query.
 */
export class CompiledInventoryReverseReferenceService {
  #cache = new Map();
  #cursorKey;
  #openedFileObserver;

  constructor({ cursor_key = null, opened_file_observer = null } = {}) {
    this.#cursorKey = cursor_key === null ? randomBytes(32) : cursor_key;
    if (opened_file_observer !== null && typeof opened_file_observer !== "function") {
      throw new TypeError("opened_file_observer must be a function");
    }
    this.#openedFileObserver = opened_file_observer;
  }

  query(args = {}) {
    if (!args || typeof args !== "object" || Array.isArray(args)) throw new TypeError("reverse-reference arguments must be an object");
    const allowed = new Set(["inventory_path", "target_uid", "folder_path", "limit", "max_work_units", "cursor"]);
    for (const key of Object.keys(args)) {
      if (!allowed.has(key)) throw new TypeError(`unknown reverse-reference argument: ${key}`);
    }
    const { inventory_path, target_uid, folder_path = "", limit = 100, max_work_units = 50_000, cursor = null } = args;
    if (typeof inventory_path !== "string" || inventory_path.length === 0) {
      throw new TypeError("inventory_path is required");
    }
    if (inventory_path.includes("\u0000")) throw new TypeError("inventory_path must not contain NUL");
    const path = resolve(inventory_path);
    const fd = openNoFollow(path);
    let cached;
    try {
      const stat = fstatSync(fd);
      assertRegularInventory(stat);
      const fingerprint = inventoryFingerprint(stat);
      this.#openedFileObserver?.(path);
      cached = this.#cache.get(path);
      if (cached?.fingerprint !== fingerprint) {
        const loaded = readOpenedInventory(fd, stat);
        cached = {
          fingerprint: loaded.fingerprint,
          index: createFolderReverseReferenceIndex(loaded.inventory, { cursor_key: this.#cursorKey })
        };
        this.#cache.delete(path);
        this.#cache.set(path, cached);
        while (this.#cache.size > MAX_CACHE_ENTRIES) this.#cache.delete(this.#cache.keys().next().value);
      } else {
        this.#cache.delete(path);
        this.#cache.set(path, cached);
      }
    } finally {
      closeSync(fd);
    }
    return cached.index.query({ target_uid, folder_path, limit, max_work_units, cursor });
  }
}
