import { readFileSync, statSync } from "node:fs";

import { createFolderReverseReferenceIndex, GRAPH_LIMITS } from "../graph/index.js";
import { stableJson } from "../format/stable.js";

const MAX_INVENTORY_BYTES = 64 * 1024 * 1024;
const MAX_KEY_FILE_BYTES = 4_096;

function positiveInteger(value, name) {
  if (!/^[1-9][0-9]*$/.test(value ?? "")) throw new TypeError(`${name} must be a positive integer`);
  const parsed = Number(value);
  if (!Number.isSafeInteger(parsed)) throw new TypeError(`${name} must be a positive safe integer`);
  return parsed;
}

function readBounded(path, maxBytes, name) {
  const stat = statSync(path);
  if (!stat.isFile()) throw new TypeError(`${name} must be a regular file`);
  if (stat.size > maxBytes) throw new RangeError(`${name} exceeds ${maxBytes} bytes`);
  const bytes = readFileSync(path);
  if (bytes.length > maxBytes) throw new RangeError(`${name} exceeds ${maxBytes} bytes`);
  return bytes;
}

function readCursorKey(path) {
  const bytes = readBounded(path, MAX_KEY_FILE_BYTES, "cursor key file");
  if (bytes.length === 32) return bytes;
  const text = bytes.toString("utf8").trim();
  if (/^[0-9a-f]{64}$/.test(text)) return Buffer.from(text, "hex");
  throw new TypeError("cursor key file must contain exactly 32 raw bytes or 64 lowercase hex digits");
}

function parseArguments(args) {
  if (args.length < 2) {
    throw new TypeError("usage: spipe reverse-references <inventory.json> <target_uid> --cursor-key-file <path> [--folder <path>] [--limit <n>] [--max-work-units <n>] [--cursor <token>]");
  }
  const options = {
    inventoryPath: args[0], targetUid: args[1], folderPath: "", limit: GRAPH_LIMITS.edge_page.default,
    maxWorkUnits: GRAPH_LIMITS.work_units.default, cursor: null, cursorKeyPath: null
  };
  const fields = new Map([
    ["--folder", "folderPath"], ["--limit", "limit"], ["--max-work-units", "maxWorkUnits"],
    ["--cursor", "cursor"], ["--cursor-key-file", "cursorKeyPath"]
  ]);
  for (let index = 2; index < args.length; index += 2) {
    const field = fields.get(args[index]);
    if (field === undefined || args[index + 1] === undefined) throw new TypeError(`invalid reverse-references argument: ${args[index]}`);
    options[field] = args[index + 1];
  }
  if (options.cursorKeyPath === null) throw new TypeError("--cursor-key-file is required for authenticated cross-process pagination");
  options.limit = positiveInteger(String(options.limit), "--limit");
  options.maxWorkUnits = positiveInteger(String(options.maxWorkUnits), "--max-work-units");
  return options;
}

function readInventory(path) {
  const bytes = readBounded(path, MAX_INVENTORY_BYTES, "compiled inventory");
  let value;
  try { value = JSON.parse(bytes.toString("utf8")); }
  catch { throw new TypeError("compiled inventory must be valid JSON"); }
  return value;
}

/** Run the public, read-only folder reverse-reference query command. */
export function runReverseReferenceCommand(command, args) {
  if (command !== "reverse-references") return { handled: false };
  const options = parseArguments(args);
  const index = createFolderReverseReferenceIndex(readInventory(options.inventoryPath), {
    cursor_key: readCursorKey(options.cursorKeyPath), indexed_target_uid: options.targetUid
  });
  const result = index.query({
    target_uid: options.targetUid,
    folder_path: options.folderPath,
    limit: options.limit,
    max_work_units: options.maxWorkUnits,
    cursor: options.cursor
  });
  console.log(stableJson(result));
  return { handled: true, result };
}
