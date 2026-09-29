import test from 'node:test';
import assert from 'node:assert/strict';
import {
  RRF_CONTRACT_V1,
  RRF_SCALE_V1,
  RRF_DEFAULT_K_V1,
  RRF_DEFAULT_SOURCE_K_V1,
  RRF_MAX_SOURCES_V1,
  RRF_MAX_DOC_ID_BYTES_V1,
  unsignedUtf8CompareV1,
  fuseRrfRawV1,
} from '../../../src/search/fusion.js';

function context(overrides = {}) {
  return {
    workspaceId: 'workspace-a',
    snapshotId: 'snapshot-a',
    authorizationScopeDigest: 'scope-a',
    queryReceipt: 'receipt-a',
    analyzerIdentity: 'analyzer-a',
    ...overrides,
  };
}

function source(name, ids, sourceIdentity = `${name}-v1`) {
  return { name, sourceIdentity, candidates: ids.map((documentId) => ({ documentId })) };
}

function request(overrides = {}) {
  return {
    context: context(),
    k: 60,
    sourceK: 1000,
    limit: 1000,
    sources: [source('lexical', ['a', 'b']), source('graph', ['b', 'a'])],
    ...overrides,
  };
}

test('exports the frozen contract constants', () => {
  assert.equal(RRF_CONTRACT_V1, 'rrf-fixed-v1');
  assert.equal(RRF_SCALE_V1, 1_000_000_000);
  assert.equal(RRF_DEFAULT_K_V1, 60);
  assert.equal(RRF_DEFAULT_SOURCE_K_V1, 1000);
  assert.equal(RRF_MAX_SOURCES_V1, 3);
  assert.equal(RRF_MAX_DOC_ID_BYTES_V1, 512);
});

test('fuses fixed-point ranks with hardcoded independent totals and explanations', () => {
  const result = fuseRrfRawV1(request());
  assert.equal(result.ok, true);
  assert.deepEqual(result.value.identity, {
    contractVersion: 'rrf-fixed-v1',
    k: 60,
    sourceK: 1000,
    orderedSources: [
      { name: 'lexical', sourceIdentity: 'lexical-v1' },
      { name: 'graph', sourceIdentity: 'graph-v1' },
    ],
    context: context(),
  });
  assert.deepEqual(result.value.hits, [
    {
      documentId: 'a',
      fusedRank: 1,
      rawScoreUnits: 32_522_474,
      contributions: [
        { source: 'lexical', sourceIdentity: 'lexical-v1', sourceRank: 1, contributionUnits: 16_393_442 },
        { source: 'graph', sourceIdentity: 'graph-v1', sourceRank: 2, contributionUnits: 16_129_032 },
      ],
    },
    {
      documentId: 'b',
      fusedRank: 2,
      rawScoreUnits: 32_522_474,
      contributions: [
        { source: 'lexical', sourceIdentity: 'lexical-v1', sourceRank: 2, contributionUnits: 16_129_032 },
        { source: 'graph', sourceIdentity: 'graph-v1', sourceRank: 1, contributionUnits: 16_393_442 },
      ],
    },
  ]);
});

test('uses semantic only when present and keeps canonical contribution order', () => {
  const result = fuseRrfRawV1(request({
    sources: [
      source('lexical', ['a', 'b']),
      source('graph', ['b', 'a']),
      source('semantic', ['a']),
    ],
  }));
  assert.equal(result.ok, true);
  assert.equal(result.value.hits[0].rawScoreUnits, 48_915_916);
  assert.deepEqual(result.value.hits[0].contributions.map((entry) => entry.source), [
    'lexical', 'graph', 'semantic',
  ]);
});

test('applies sourceK after validating the full supplied page and limit after merging', () => {
  const lexical = source('lexical', ['first', 'ignored', 'ignored']);
  const invalid = fuseRrfRawV1(request({ sourceK: 1, sources: [lexical, source('graph', [])] }));
  assert.deepEqual(invalid, {
    ok: false,
    error: { code: 'duplicate_document_id', source: 'lexical', candidateIndex: 2 },
  });

  const valid = fuseRrfRawV1(request({
    sourceK: 1,
    limit: 1,
    sources: [source('lexical', ['z', 'ignored']), source('graph', ['a', 'ignored-2'])],
  }));
  assert.equal(valid.ok, true);
  assert.deepEqual(valid.value.hits, [{
    documentId: 'a',
    fusedRank: 1,
    rawScoreUnits: 16_393_442,
    contributions: [{
      source: 'graph', sourceIdentity: 'graph-v1', sourceRank: 1, contributionUnits: 16_393_442,
    }],
  }]);
});

test('uses unsigned UTF-8 byte ordering for score ties', () => {
  const result = fuseRrfRawV1(request({
    sources: [source('lexical', ['é', 'z']), source('graph', ['z', 'é'])],
  }));
  assert.equal(result.ok, true);
  assert.deepEqual(result.value.hits.map((hit) => hit.documentId), ['z', 'é']);

  const astral = fuseRrfRawV1(request({
    sources: [source('lexical', ['𐀀', 'é']), source('graph', ['é', '𐀀'])],
  }));
  assert.deepEqual(astral.value.hits.map((hit) => hit.documentId), ['é', '𐀀']);
  assert.ok(unsignedUtf8CompareV1('z', 'é') < 0);
  assert.ok(unsignedUtf8CompareV1('é', '𐀀') < 0);
});

test('rejects unpaired surrogates and enforces UTF-8 byte rather than code-unit limits', () => {
  const bad = fuseRrfRawV1(request({
    sources: [source('lexical', ['\ud800']), source('graph', [])],
  }));
  assert.deepEqual(bad, {
    ok: false,
    error: { code: 'invalid_document_id', source: 'lexical', candidateIndex: 0 },
  });
  const boundary = 'é'.repeat(256);
  assert.equal(fuseRrfRawV1(request({
    sources: [source('lexical', [boundary]), source('graph', [])],
  })).ok, true);
  assert.deepEqual(fuseRrfRawV1(request({
    sources: [source('lexical', [`${boundary}a`]), source('graph', [])],
  })), {
    ok: false,
    error: { code: 'document_id_too_large', source: 'lexical', candidateIndex: 0 },
  });
});

test('binds context and source identities without retaining caller objects', () => {
  const input = request();
  const before = structuredClone(input);
  const first = fuseRrfRawV1(input);
  assert.deepEqual(input, before);
  input.context.workspaceId = 'changed-after-call';
  input.sources[0].sourceIdentity = 'changed-after-call';
  assert.equal(first.value.identity.context.workspaceId, 'workspace-a');
  assert.equal(first.value.identity.orderedSources[0].sourceIdentity, 'lexical-v1');

  const changedContext = fuseRrfRawV1(request({ context: context({ snapshotId: 'snapshot-b' }) }));
  const changedSource = fuseRrfRawV1(request({
    sources: [source('lexical', ['a', 'b'], 'lexical-v2'), source('graph', ['b', 'a'])],
  }));
  assert.notDeepEqual(first.value.identity, changedContext.value.identity);
  assert.notDeepEqual(first.value.identity, changedSource.value.identity);
});

test('validates request and context before numeric and source fields', () => {
  assert.deepEqual(fuseRrfRawV1(null), { ok: false, error: { code: 'invalid_request' } });
  assert.deepEqual(fuseRrfRawV1({ extra: true }), { ok: false, error: { code: 'invalid_request' } });
  assert.deepEqual(fuseRrfRawV1({ context: {}, k: 0, sources: [] }), {
    ok: false, error: { code: 'invalid_context', field: 'workspaceId' },
  });
  assert.deepEqual(fuseRrfRawV1(request({ k: 0, sourceK: 0, limit: 0, sources: [] })), {
    ok: false, error: { code: 'invalid_k' },
  });
  assert.deepEqual(fuseRrfRawV1(request({ sourceK: 0, limit: 0, sources: [] })), {
    ok: false, error: { code: 'invalid_source_k' },
  });
  assert.deepEqual(fuseRrfRawV1(request({ limit: 0, sources: [] })), {
    ok: false, error: { code: 'invalid_limit' },
  });
  assert.deepEqual(fuseRrfRawV1(request({ sources: [] })), {
    ok: false, error: { code: 'invalid_sources' },
  });
});

test('enforces required canonical sources, closed shapes, bounds, and duplicate precedence', () => {
  assert.deepEqual(fuseRrfRawV1(request({
    sources: [source('graph', []), source('semantic', [])],
  })), { ok: false, error: { code: 'missing_required_source', source: 'lexical' } });
  assert.deepEqual(fuseRrfRawV1(request({
    sources: [source('lexical', []), source('semantic', [])],
  })), { ok: false, error: { code: 'missing_required_source', source: 'graph' } });
  assert.deepEqual(fuseRrfRawV1(request({
    sources: [source('graph', []), source('lexical', [])],
  })), { ok: false, error: { code: 'invalid_source_order', source: 'graph' } });
  assert.deepEqual(fuseRrfRawV1(request({
    sources: [source('lexical', []), source('graph', []), source('graph', [])],
  })), { ok: false, error: { code: 'duplicate_source' } });

  const tooMany = Array.from({ length: 1001 }, (_, index) => `d-${index}`);
  assert.deepEqual(fuseRrfRawV1(request({
    sources: [source('lexical', tooMany), source('graph', [])],
  })), { ok: false, error: { code: 'too_many_candidates', source: 'lexical' } });

  const extraCandidate = source('lexical', ['a']);
  extraCandidate.candidates[0].score = 1;
  assert.deepEqual(fuseRrfRawV1(request({
    sources: [extraCandidate, source('graph', [])],
  })), {
    ok: false, error: { code: 'invalid_candidate', source: 'lexical', candidateIndex: 0 },
  });
});

test('never throws for hostile caller data', () => {
  const hostile = new Proxy({}, { ownKeys() { throw new Error('hostile'); } });
  assert.doesNotThrow(() => fuseRrfRawV1(hostile));
  assert.deepEqual(fuseRrfRawV1(hostile), { ok: false, error: { code: 'invalid_request' } });
});

test('rank 1000 uses the frozen integer-floor contribution', () => {
  const ids = Array.from({ length: 1000 }, (_, index) => `id-${String(index).padStart(4, '0')}`);
  const result = fuseRrfRawV1(request({
    sources: [source('lexical', ids), source('graph', [])],
  }));
  assert.equal(result.ok, true);
  const last = result.value.hits.find((hit) => hit.documentId === 'id-0999');
  assert.equal(last.rawScoreUnits, 943_396);
  assert.equal(last.contributions[0].sourceRank, 1000);
});
