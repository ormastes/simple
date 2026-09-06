import type { ExtensionHostServices } from '../services/extensionHostServices';
export type SimpleLspAuthority = 'authoritative' | 'degraded';
export type SimpleLspCoverage = 'semantic' | 'syntax-only';
export type SimpleLspSource = 'native' | 'wasm' | 'fallback';
export interface SimpleLspCapabilityReceipt {
    authority: SimpleLspAuthority;
    coverage: SimpleLspCoverage;
    source: SimpleLspSource;
    fallbackActive: boolean;
    message: string;
    detail?: string;
}
export interface SimpleLspFallbackControl {
    setEnabled(enabled: boolean): void;
}
export declare function authoritativeLspReceipt(source: Exclude<SimpleLspSource, 'fallback'>): SimpleLspCapabilityReceipt;
export declare function degradedLspReceipt(message: string, detail?: string): SimpleLspCapabilityReceipt;
export declare function publishLspCapabilityReceipt(services: ExtensionHostServices, controls: readonly SimpleLspFallbackControl[], receipt: SimpleLspCapabilityReceipt): void;
