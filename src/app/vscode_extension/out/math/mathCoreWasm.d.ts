import * as vscode from 'vscode';
export interface MathCoreRenderResult {
    latex?: string;
    pretty?: string;
    text?: string;
    debug?: string;
    svg?: string;
    html?: string;
}
export declare class MathCoreWasmBridge {
    private status;
    private exports;
    private renderFunction;
    private allocFunction;
    private freeFunction;
    private unavailableReason;
    initialize(extensionUri: vscode.Uri): Promise<void>;
    isReady(): boolean;
    getUnavailableReason(): string | undefined;
    render(source: string): Promise<MathCoreRenderResult | undefined>;
    private markUnavailable;
    private resolveRenderFunction;
    private resolveAllocFunction;
    private resolveFreeFunction;
    private usesSizedOutput;
    private isSmfArtifact;
    private freeBuffer;
    private readLength;
    private readFixedLengthString;
    private readNullTerminatedString;
}
