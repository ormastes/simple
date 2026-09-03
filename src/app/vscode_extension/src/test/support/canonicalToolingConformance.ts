import * as vscode from 'vscode';

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

export async function loadCanonicalToolingConformanceV1(): Promise<CanonicalToolingConformanceV1> {
    const extension = vscode.extensions.getExtension('simple-lang.simple-rich-editor');
    if (!extension) {
        throw new Error('Simple extension is unavailable');
    }
    const uri = vscode.Uri.joinPath(extension.extensionUri, 'test-fixtures', 'canonical-tooling-conformance-v1.sdn');
    const bytes = await vscode.workspace.fs.readFile(uri);
    const parsed = JSON.parse(new TextDecoder().decode(bytes)) as Partial<CanonicalToolingConformanceV1>;
    if (parsed.schema !== 'simple.tooling.ide-conformance/1'
        || parsed.language !== 'simple'
        || parsed.authority !== 'authoritative'
        || parsed.coverage !== 'semantic'
        || parsed.native_source !== 'native'
        || parsed.browser_source !== 'wasm'
        || parsed.semantic_coverage_complete !== true
        || typeof parsed.uri !== 'string'
        || typeof parsed.revision !== 'number'
        || typeof parsed.content_digest !== 'string'
        || typeof parsed.canonical_result_id !== 'string') {
        throw new Error('Malformed canonical tooling conformance corpus');
    }
    return parsed as CanonicalToolingConformanceV1;
}
