import { createHash } from 'node:crypto';

import { canonicalJson, freezeDeep } from '../storage/canonical.js';

export const RRF_CONTRACT_V1 = 'rrf-fixed-v1';
export const RRF_SCALE_V1 = 1_000_000_000;
export const RRF_DEFAULT_K_V1 = 60;
export const RRF_DEFAULT_SOURCE_K_V1 = 1000;
export const RRF_DEFAULT_LIMIT_V1 = 1000;
export const RRF_MAX_SOURCES_V1 = 3;
export const RRF_MAX_DOC_ID_BYTES_V1 = 512;
export const RRF_POOL_CONTRACT_V2 = 'rrf-complete-pool-v2';
export const RRF_ARITHMETIC_CONTRACT_V2 = RRF_CONTRACT_V1;
export const RRF_MAX_SOURCE_K_V2 = 1000;
export const RRF_MAX_POOL_HITS_V2 = 3000;
export const RRF_MAX_PUBLIC_HITS_V2 = 1000;

const CONTEXT_FIELDS = Object.freeze([
  'workspaceId',
  'snapshotId',
  'authorizationScopeDigest',
  'queryReceipt',
  'analyzerIdentity',
]);
const REQUEST_FIELDS = new Set(['context', 'k', 'sourceK', 'limit', 'sources']);
const CONTEXT_FIELD_SET = new Set(CONTEXT_FIELDS);
const SOURCE_FIELDS = new Set(['name', 'sourceIdentity', 'candidates']);
const CANDIDATE_FIELDS = new Set(['documentId']);
const SOURCE_ORDER = Object.freeze(['lexical', 'graph', 'semantic']);

function failure(code, details) {
  return { ok: false, error: details === undefined ? { code } : { code, ...details } };
}

function isRecord(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

function hasOnlyKeys(value, allowed) {
  return Object.keys(value).every((key) => allowed.has(key));
}

function utf8BytesV1(value) {
  const bytes = [];
  for (let index = 0; index < value.length; index += 1) {
    let scalar = value.charCodeAt(index);
    if (scalar >= 0xd800 && scalar <= 0xdbff) {
      if (index + 1 >= value.length) return null;
      const low = value.charCodeAt(index + 1);
      if (low < 0xdc00 || low > 0xdfff) return null;
      scalar = 0x10000 + ((scalar - 0xd800) << 10) + (low - 0xdc00);
      index += 1;
    } else if (scalar >= 0xdc00 && scalar <= 0xdfff) {
      return null;
    }

    if (scalar <= 0x7f) {
      bytes.push(scalar);
    } else if (scalar <= 0x7ff) {
      bytes.push(0xc0 | (scalar >> 6), 0x80 | (scalar & 0x3f));
    } else if (scalar <= 0xffff) {
      bytes.push(
        0xe0 | (scalar >> 12),
        0x80 | ((scalar >> 6) & 0x3f),
        0x80 | (scalar & 0x3f),
      );
    } else {
      bytes.push(
        0xf0 | (scalar >> 18),
        0x80 | ((scalar >> 12) & 0x3f),
        0x80 | ((scalar >> 6) & 0x3f),
        0x80 | (scalar & 0x3f),
      );
    }
  }
  return bytes;
}

export function unsignedUtf8CompareV1(left, right) {
  const leftBytes = utf8BytesV1(left);
  const rightBytes = utf8BytesV1(right);
  if (leftBytes === null || rightBytes === null) return 0;
  const shared = Math.min(leftBytes.length, rightBytes.length);
  for (let index = 0; index < shared; index += 1) {
    if (leftBytes[index] !== rightBytes[index]) return leftBytes[index] - rightBytes[index];
  }
  return leftBytes.length - rightBytes.length;
}

function validBoundedString(value, maximumBytes) {
  if (typeof value !== 'string' || value.length === 0) return false;
  const bytes = utf8BytesV1(value);
  return bytes !== null && bytes.length <= maximumBytes;
}

export function fuseRrfRawV1(request) {
  try {
    if (!isRecord(request) || !hasOnlyKeys(request, REQUEST_FIELDS)) {
      return failure('invalid_request');
    }

    const context = request.context;
    for (const field of CONTEXT_FIELDS) {
      if (
        !isRecord(context)
        || !hasOnlyKeys(context, CONTEXT_FIELD_SET)
        || !validBoundedString(context[field], RRF_MAX_DOC_ID_BYTES_V1)
      ) {
        return failure('invalid_context', { field });
      }
    }

    const k = request.k === undefined ? RRF_DEFAULT_K_V1 : request.k;
    if (!Number.isSafeInteger(k) || k < 1 || k > 10_000) return failure('invalid_k');

    const sourceK = request.sourceK === undefined
      ? RRF_DEFAULT_SOURCE_K_V1
      : request.sourceK;
    if (!Number.isSafeInteger(sourceK) || sourceK < 1 || sourceK > 1000) {
      return failure('invalid_source_k');
    }

    const limit = request.limit === undefined ? 1000 : request.limit;
    if (!Number.isSafeInteger(limit) || limit < 1 || limit > 1000) {
      return failure('invalid_limit');
    }

    const sources = request.sources;
    if (!Array.isArray(sources) || sources.length < 2 || sources.length > RRF_MAX_SOURCES_V1) {
      return failure('invalid_sources');
    }

    const names = sources.map((source) => isRecord(source) ? source.name : undefined);
    if (!names.includes('lexical')) return failure('missing_required_source', { source: 'lexical' });
    if (!names.includes('graph')) return failure('missing_required_source', { source: 'graph' });

    let previousSourceOrdinal = -1;
    for (const name of names) {
      const sourceOrdinal = SOURCE_ORDER.indexOf(name);
      if (sourceOrdinal < 0 || sourceOrdinal < previousSourceOrdinal) {
        return failure('invalid_source_order', { source: name });
      }
      previousSourceOrdinal = sourceOrdinal;
    }
    if (new Set(names).size !== names.length) return failure('duplicate_source');

    const accumulated = new Map();
    const orderedSources = [];
    for (const source of sources) {
      if (!isRecord(source) || !hasOnlyKeys(source, SOURCE_FIELDS)) {
        return failure('invalid_source_identity', { source: source && source.name });
      }
      if (!validBoundedString(source.sourceIdentity, RRF_MAX_DOC_ID_BYTES_V1)) {
        return failure('invalid_source_identity', { source: source.name });
      }
      if (!Array.isArray(source.candidates) || source.candidates.length > 1000) {
        return failure('too_many_candidates', { source: source.name });
      }

      const seenDocumentIds = new Set();
      for (let candidateIndex = 0; candidateIndex < source.candidates.length; candidateIndex += 1) {
        const candidate = source.candidates[candidateIndex];
        if (!isRecord(candidate) || !hasOnlyKeys(candidate, CANDIDATE_FIELDS)) {
          return failure('invalid_candidate', { source: source.name, candidateIndex });
        }
        if (typeof candidate.documentId !== 'string' || candidate.documentId.length === 0) {
          return failure('invalid_document_id', { source: source.name, candidateIndex });
        }
        const documentIdBytes = utf8BytesV1(candidate.documentId);
        if (documentIdBytes === null) {
          return failure('invalid_document_id', { source: source.name, candidateIndex });
        }
        if (documentIdBytes.length > RRF_MAX_DOC_ID_BYTES_V1) {
          return failure('document_id_too_large', { source: source.name, candidateIndex });
        }
        if (seenDocumentIds.has(candidate.documentId)) {
          return failure('duplicate_document_id', { source: source.name, candidateIndex });
        }
        seenDocumentIds.add(candidate.documentId);
      }

      orderedSources.push({ name: source.name, sourceIdentity: source.sourceIdentity });
      const acceptedCount = Math.min(sourceK, source.candidates.length);
      for (let index = 0; index < acceptedCount; index += 1) {
        const documentId = source.candidates[index].documentId;
        const sourceRank = index + 1;
        const contributionUnits = Math.floor(RRF_SCALE_V1 / (k + sourceRank));
        let record = accumulated.get(documentId);
        if (record === undefined) {
          record = { documentId, rawScoreUnits: 0, contributions: [] };
          accumulated.set(documentId, record);
        }
        record.rawScoreUnits += contributionUnits;
        record.contributions.push({
          source: source.name,
          sourceIdentity: source.sourceIdentity,
          sourceRank,
          contributionUnits,
        });
      }
    }

    const ranked = Array.from(accumulated.values());
    ranked.sort((left, right) => {
      if (left.rawScoreUnits !== right.rawScoreUnits) {
        return right.rawScoreUnits - left.rawScoreUnits;
      }
      return unsignedUtf8CompareV1(left.documentId, right.documentId);
    });

    const hits = ranked.slice(0, limit).map((hit, index) => ({
      documentId: hit.documentId,
      fusedRank: index + 1,
      rawScoreUnits: hit.rawScoreUnits,
      contributions: hit.contributions,
    }));

    return {
      ok: true,
      value: {
        identity: {
          contractVersion: RRF_CONTRACT_V1,
          k,
          sourceK,
          orderedSources,
          context: Object.fromEntries(CONTEXT_FIELDS.map((field) => [field, context[field]])),
        },
        hits,
      },
    };
  } catch (_error) {
    return failure('invalid_request');
  }
}

const RRF_SOURCE_POOL_DOMAIN_V2 = 'spipe-rrf-source-pool-v1\0';
const RRF_COMPLETE_SOURCE_SET_DOMAIN_V2 = 'spipe-rrf-complete-source-set-v1\0';
const RRF_COMPLETE_OUTPUT_DOMAIN_V2 = 'spipe-rrf-complete-output-v1\0';

function rrfDigestV2(domain, value) {
  return `sha256:${createHash('sha256').update(domain, 'utf8').update(canonicalJson(value), 'utf8').digest('hex')}`;
}

function rrfCandidateDigestV2(name, sourceIdentity, documentIds) {
  return rrfDigestV2(RRF_SOURCE_POOL_DOMAIN_V2, { name, sourceIdentity, documentIds });
}

function rrfSourcePoolDigestV2(sources) {
  return rrfDigestV2(RRF_COMPLETE_SOURCE_SET_DOMAIN_V2, sources.map((source) => ({
    name: source.name,
    sourceIdentity: source.sourceIdentity,
    complete: source.complete,
    candidateCount: source.candidateCount,
    candidateDigest: source.candidateDigest,
  })));
}

/** Fuse complete, digest-bound source pools without exposing a truncated pool. */
export function fuseRrfCompletePoolV2(request) {
  try {
    if (!isRecord(request) || !hasOnlyKeys(request, new Set(['context', 'k', 'sourceK', 'sources']))) return failure('invalid_request');
    const context = request.context;
    if (!isRecord(context) || !hasOnlyKeys(context, CONTEXT_FIELD_SET)) return failure('invalid_context', { field: CONTEXT_FIELDS[0] });
    for (const field of CONTEXT_FIELDS) if (!validBoundedString(context[field], RRF_MAX_DOC_ID_BYTES_V1)) return failure('invalid_context', { field });
    const k = request.k === undefined ? RRF_DEFAULT_K_V1 : request.k;
    const sourceK = request.sourceK === undefined ? RRF_DEFAULT_SOURCE_K_V1 : request.sourceK;
    if (!Number.isSafeInteger(k) || k < 1 || k > 10_000) return failure('invalid_k');
    if (!Number.isSafeInteger(sourceK) || sourceK < 1 || sourceK > RRF_MAX_SOURCE_K_V2) return failure('invalid_source_k');
    if (!Array.isArray(request.sources) || request.sources.length < 2 || request.sources.length > RRF_MAX_SOURCES_V1) return failure('invalid_sources');

    const sources = [];
    let previousOrdinal = -1;
    const names = request.sources.map((source) => isRecord(source) ? source.name : undefined);
    if (!names.includes('lexical')) return failure('missing_required_source', { source: 'lexical' });
    if (!names.includes('graph')) return failure('missing_required_source', { source: 'graph' });
    for (const name of names) {
      const ordinal = SOURCE_ORDER.indexOf(name);
      if (ordinal < 0 || ordinal < previousOrdinal) return failure('invalid_source_order', { source: name });
      previousOrdinal = ordinal;
    }
    if (new Set(names).size !== names.length) return failure('duplicate_source');

    for (const source of request.sources) {
      if (!isRecord(source) || !hasOnlyKeys(source, new Set(['name', 'sourceIdentity', 'complete', 'candidateCount', 'candidateDigest', 'candidates']))) {
        return failure('invalid_source_identity', { source: source?.name });
      }
      if (!validBoundedString(source.sourceIdentity, RRF_MAX_DOC_ID_BYTES_V1)) return failure('invalid_source_identity', { source: source.name });
      if (source.complete !== true) return failure('incomplete_source_page', { source: source.name });
      if (!Number.isSafeInteger(source.candidateCount) || source.candidateCount < 0) return failure('invalid_candidate_count', { source: source.name });
      if (!Array.isArray(source.candidates) || source.candidates.length !== source.candidateCount) return failure('invalid_candidate_page', { source: source.name });
      if (source.candidateCount > sourceK || source.candidateCount > RRF_MAX_SOURCE_K_V2) return failure('too_many_candidates', { source: source.name });
      const seen = new Set();
      const documentIds = [];
      for (let index = 0; index < source.candidates.length; index += 1) {
        const candidate = source.candidates[index];
        if (!isRecord(candidate) || !hasOnlyKeys(candidate, CANDIDATE_FIELDS) || !validBoundedString(candidate.documentId, RRF_MAX_DOC_ID_BYTES_V1)) return failure('invalid_candidate', { source: source.name, candidateIndex: index });
        if (seen.has(candidate.documentId)) return failure('duplicate_document_id', { source: source.name, candidateIndex: index });
        seen.add(candidate.documentId); documentIds.push(candidate.documentId);
      }
      const candidateDigest = rrfCandidateDigestV2(source.name, source.sourceIdentity, documentIds);
      if (source.candidateDigest !== candidateDigest) return failure('candidate_digest_mismatch', { source: source.name });
      sources.push({ name: source.name, sourceIdentity: source.sourceIdentity, complete: true, candidateCount: source.candidateCount, candidateDigest, candidates: source.candidates });
    }

    const accumulated = new Map();
    for (const source of sources) for (let index = 0; index < source.candidates.length; index += 1) {
      const documentId = source.candidates[index].documentId;
      let hit = accumulated.get(documentId);
      if (!hit) {
        if (accumulated.size >= RRF_MAX_POOL_HITS_V2) return failure('pool_too_large');
        hit = { documentId, rawScoreUnits: 0, contributions: [] }; accumulated.set(documentId, hit);
      }
      const sourceRank = index + 1;
      const contributionUnits = Math.floor(RRF_SCALE_V1 / (k + sourceRank));
      const nextScore = hit.rawScoreUnits + contributionUnits;
      if (!Number.isSafeInteger(nextScore)) return failure('arithmetic_overflow');
      hit.rawScoreUnits = nextScore;
      hit.contributions.push({ source: source.name, sourceIdentity: source.sourceIdentity, sourceRank, contributionUnits });
    }
    const ranked = Array.from(accumulated.values()).sort((left, right) => left.rawScoreUnits === right.rawScoreUnits
      ? unsignedUtf8CompareV1(left.documentId, right.documentId) : right.rawScoreUnits - left.rawScoreUnits);
    const hits = ranked.map((hit, index) => ({ documentId: hit.documentId, fusedRank: index + 1, rawScoreUnits: hit.rawScoreUnits, contributions: hit.contributions }));
    const orderedSources = sources.map(({ name, sourceIdentity, complete, candidateCount, candidateDigest }) => ({ name, sourceIdentity, complete, candidateCount, candidateDigest }));
    const identity = { contractVersion: RRF_POOL_CONTRACT_V2, arithmeticContractVersion: RRF_ARITHMETIC_CONTRACT_V2, k, sourceK, orderedSources, context: Object.fromEntries(CONTEXT_FIELDS.map((field) => [field, context[field]])), complete: true, uniqueDocumentCount: hits.length, sourcePoolDigest: rrfSourcePoolDigestV2(orderedSources) };
    const rawFusionDigest = rrfDigestV2(RRF_COMPLETE_OUTPUT_DOMAIN_V2, { identity, hits });
    return freezeDeep({ ok: true, value: { identity: { ...identity, rawFusionDigest }, hits } });
  } catch (_error) {
    return failure('invalid_request');
  }
}
