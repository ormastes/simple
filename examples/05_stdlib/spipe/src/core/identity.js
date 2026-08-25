import { createHash } from "node:crypto";

export const IDENTITY_VERSION = "spipe-identity-v1";

function freeze(value, seen = new WeakSet()) {
  if (!value || typeof value !== "object" || seen.has(value)) return value;
  seen.add(value);
  for (const child of Object.values(value)) freeze(child, seen);
  return Object.freeze(value);
}

function clone(value) {
  if (Array.isArray(value)) return value.map(clone);
  if (!value || typeof value !== "object") return value;
  return Object.fromEntries(Object.entries(value).map(([key, child]) => [key, clone(child)]));
}

function text(value) {
  return value === undefined || value === null ? "" : String(value);
}

export function normalizeText(value) {
  return text(value).normalize("NFC").trim();
}

export function normalizeSemanticKey(value) {
  return normalizeText(value)
    .toLocaleLowerCase("en-US")
    .replace(/[\\/\s]+/g, ".")
    .replace(/\.+/g, ".")
    .replace(/^\.+|\.+$/g, "");
}

export function normalizeAlias(value) {
  return normalizeSemanticKey(value);
}

export function slugify(value) {
  return normalizeText(value)
    .toLocaleLowerCase("en-US")
    .replace(/[^\p{Letter}\p{Number}]+/gu, "-")
    .replace(/^-+|-+$/g, "") || "untitled";
}

export function canonicalPath(value) {
  const raw = normalizeText(value).replaceAll("\\", "/");
  const segments = [];
  for (const part of raw.split("/")) {
    if (!part || part === ".") continue;
    if (part === "..") return { path: raw, valid: false };
    segments.push(part);
  }
  return { path: segments.join("/"), valid: !raw.startsWith("/") && !/^[A-Za-z]:/.test(raw) };
}

export function sha256(value) {
  return createHash("sha256").update(text(value), "utf8").digest("hex");
}

export function contentHash(value) {
  return `sha256:${sha256(value)}`;
}

function hashUid(prefix, tuple) {
  return `${prefix}-${sha256(tuple).slice(0, 32)}`;
}

export function provisionalArtifactUid(projectUid, bytesOrHash) {
  const project = normalizeText(projectUid) || "unregistered";
  const hash = normalizeText(bytesOrHash).replace(/^sha256:/, "") || sha256(bytesOrHash);
  return `P-${project}-${hash}`;
}

export function proposedArtifactUid({ projectUid = "unregistered", canonicalPath: path = "", contentHash: hash = "" } = {}) {
  return hashUid("A", `artifact_uid_proposal_v1\0${normalizeText(projectUid)}\0${normalizeText(path)}\0${normalizeText(hash)}`);
}

export function proposedSectionUid({ artifactUid = "", ordinal = 0, key = "" } = {}) {
  return hashUid("S", `section_uid_proposal_v1\0${normalizeText(artifactUid)}\0${ordinal}\0${normalizeSemanticKey(key)}`);
}

export function identityStatus(uid) {
  return normalizeText(uid).startsWith("P-") ? "provisional" : "authoritative";
}

function diagnostic(code, severity, messageKey, details = {}) {
  return freeze({ code, severity, message_key: messageKey, details: freeze({ ...details }) });
}

function candidateRecord(uid, kind, record, field) {
  return { uid, kind, record: clone(record), field };
}

function recordParts(item) {
  const artifact = item?.artifact && typeof item.artifact === "object" ? item.artifact : item;
  const sections = Array.isArray(item?.sections) ? item.sections : [];
  return { artifact: artifact || {}, sections };
}

function keyFor(record) {
  return normalizeSemanticKey(record.key);
}

function aliasesFor(record) {
  return (Array.isArray(record.aliases) ? record.aliases : [])
    .map(normalizeAlias)
    .filter(Boolean);
}

function immutableMapEntries(map) {
  return Object.fromEntries([...map.entries()].sort(([a], [b]) => a.localeCompare(b)).map(([key, values]) => [
    key,
    values.map((value) => freeze({ ...value })),
  ]));
}

/**
 * Build an immutable UID/key/alias index from parser records.
 *
 * The index never silently chooses a winner. A duplicate UID is SPK001 and
 * any key/alias with more than one visible target is SPK002. Consumers may
 * still inspect all records in an advisory snapshot, but `resolve` returns
 * an ambiguity result instead of guessing.
 */
export function buildIdentityIndex(records = []) {
  const items = Array.isArray(records)
    ? records
    : Array.isArray(records?.artifacts) ? records.artifacts : [records];
  const byUid = new Map();
  const byKey = new Map();
  const byAlias = new Map();
  const diagnostics = [];

  const addUid = (uid, kind, record, field) => {
    const normalized = normalizeText(uid);
    if (!normalized) return;
    const previous = byUid.get(normalized) || [];
    if (previous.length) diagnostics.push(diagnostic(
      "SPK001", "error", "identity.duplicate_uid", { uid: normalized, kind, field },
    ));
    previous.push(candidateRecord(normalized, kind, record, field));
    byUid.set(normalized, previous);
  };
  const addName = (map, name, uid, kind, record, field) => {
    const normalized = map === byAlias ? normalizeAlias(name) : normalizeSemanticKey(name);
    if (!normalized) return;
    const previous = map.get(normalized) || [];
    previous.push(candidateRecord(uid, kind, record, field));
    map.set(normalized, previous);
  };

  for (const item of items) {
    const { artifact, sections } = recordParts(item);
    const artifactUid = normalizeText(artifact.uid);
    if (artifactUid) {
      addUid(artifactUid, "artifact", artifact, "uid");
      if (artifact.key) addName(byKey, artifact.key, artifactUid, "artifact", artifact, "key");
      for (const alias of aliasesFor(artifact)) addName(byAlias, alias, artifactUid, "artifact", artifact, "alias");
    }
    for (const section of sections) {
      const sectionUid = normalizeText(section.uid);
      if (!sectionUid) continue;
      addUid(sectionUid, "section", section, "uid");
      if (section.key) addName(byKey, section.key, sectionUid, "section", section, "key");
      for (const alias of aliasesFor(section)) addName(byAlias, alias, sectionUid, "section", section, "alias");
    }
  }

  const ambiguous = (map, label) => {
    for (const [name, values] of map.entries()) {
      const unique = [...new Set(values.map((value) => value.uid))];
      if (unique.length > 1) diagnostics.push(diagnostic(
        "SPK002", "error", "identity.ambiguous_alias", { name, label, candidates: unique.sort() },
      ));
    }
  };
  ambiguous(byKey, "key");
  ambiguous(byAlias, "alias");

  const frozenByUid = immutableMapEntries(byUid);
  const frozenByKey = immutableMapEntries(byKey);
  const frozenByAlias = immutableMapEntries(byAlias);
  const sortedDiagnostics = diagnostics.sort((left, right) => JSON.stringify(left).localeCompare(JSON.stringify(right)));
  const index = {
    version: IDENTITY_VERSION,
    by_uid: frozenByUid,
    by_key: frozenByKey,
    by_alias: frozenByAlias,
    diagnostics: sortedDiagnostics,
  };
  Object.defineProperty(index, "resolve", {
    enumerable: true,
    value: (value) => resolveIdentity(index, value),
  });
  return freeze(index);
}

export function resolveIdentity(index, value) {
  const raw = normalizeText(value);
  if (!raw) return freeze({ status: "not_found", value: raw, candidates: [] });
  const direct = index.by_uid[raw] || [];
  const key = normalizeSemanticKey(raw);
  const alias = normalizeAlias(raw);
  const matches = direct.length ? direct : (index.by_key[key] || index.by_alias[alias] || []);
  const unique = [...new Map(matches.map((candidate) => [candidate.uid, candidate])).values()]
    .sort((left, right) => left.uid.localeCompare(right.uid));
  if (!unique.length) return freeze({ status: "not_found", value: raw, candidates: [] });
  if (unique.length > 1) return freeze({ status: "ambiguous", value: raw, candidates: unique });
  return freeze({ status: "resolved", value: raw, candidate: unique[0], candidates: unique });
}

/**
 * Return deterministic, dry-run marker insertion proposals. This function is
 * intentionally incapable of writing files; applying a proposal belongs to
 * the later RefactorService wave.
 */
export function planUidInjection(parsed, options = {}) {
  const records = Array.isArray(parsed) ? parsed : [parsed];
  const proposals = [];
  for (const item of records) {
    const artifact = item?.artifact && typeof item.artifact === "object" ? item.artifact : item;
    if (!artifact || artifact.uid === undefined || artifact.identity_status !== "provisional") continue;
    const path = artifact.canonical_path || artifact.canonicalPath || "";
    const proposedUid = proposedArtifactUid({
      projectUid: artifact.project_uid || artifact.projectUid,
      canonicalPath: path,
      contentHash: artifact.content_hash || artifact.contentHash,
    });
    const marker = `<!-- spipe:artifact uid=${proposedUid} key=${artifact.key || slugify(artifact.title)} -->\n`;
    proposals.push({
      kind: "artifact_uid",
      path,
      proposed_uid: proposedUid,
      offset: Number.isInteger(options.artifactOffset) ? options.artifactOffset : 0,
      insertion: marker,
      operation: "insert_marker",
      canonical_mutation: false,
      reason: "missing_artifact_uid",
    });
    for (const section of item.sections || []) {
      if (section.uid) continue;
      const sectionUid = proposedSectionUid({ artifactUid: proposedUid, ordinal: section.ordinal, key: section.key || section.heading });
      proposals.push({
        kind: "section_uid",
        path,
        proposed_uid: sectionUid,
        heading: section.heading,
        ordinal: section.ordinal,
        offset: section.marker_offset ?? section.heading_end_offset,
        insertion: `<!-- spipe:section uid=${sectionUid} key=${section.key || slugify(section.heading)} -->\n`,
        operation: "insert_marker",
        canonical_mutation: false,
        reason: "missing_section_uid",
      });
    }
  }
  return freeze(proposals.sort((left, right) => `${left.path}\0${left.offset}\0${left.kind}`.localeCompare(`${right.path}\0${right.offset}\0${right.kind}`)));
}

export function planUidInjections(parsed, options = {}) {
  return planUidInjection(parsed, options);
}
