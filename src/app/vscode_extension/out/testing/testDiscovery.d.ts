import * as vscode from 'vscode';
export type TestBlockKind = 'describe' | 'context' | 'it' | 'sdoctest';
export interface TestBlock {
    kind: TestBlockKind;
    label: string;
    line: number;
}
export declare function detectTestBlocks(document: vscode.TextDocument): TestBlock[];
