import { ExtensionHostServices } from '../services/extensionHostServices';
import { SimpleLspBootstrapHook } from './simpleLspCompatibility';
import { SimpleLspFallbackControl } from './simpleLspCapabilityReceipt';
export interface CreateSimpleLspClientBootstrapOptions {
    services: ExtensionHostServices;
    onRunningStateChanged?: (running: boolean) => void;
    fallbackControls?: SimpleLspFallbackControl[];
}
export declare function createSimpleLspClientBootstrap(options: CreateSimpleLspClientBootstrapOptions): SimpleLspBootstrapHook;
