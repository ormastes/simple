export interface CanonicalToolingConformanceV1 {
    schema: 'simple.tooling.ide-conformance/1';
    uri: string;
    language: 'simple';
    revision: number;
    content_digest: string;
    canonical_result_id: string;
    authority: 'authoritative';
    coverage: 'semantic';
    native_source: 'native';
    browser_source: 'wasm';
    semantic_coverage_complete: true;
}
export declare function loadCanonicalToolingConformanceV1(): Promise<CanonicalToolingConformanceV1>;
