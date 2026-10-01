export interface KpfCommandContribution {
    readonly command: string;
    readonly title: string;
    readonly category: string;
    readonly requiredCapability?: string;
}
export interface KpfContributionProjection {
    readonly schemaVersion: 1;
    readonly activationEvents: readonly string[];
    readonly commands: readonly KpfCommandContribution[];
}
export declare const GENERATED_KPF_CONTRIBUTIONS: KpfContributionProjection;
export declare function projectContributionCommands(projection: KpfContributionProjection, admittedCapabilities: ReadonlySet<string>): readonly KpfCommandContribution[];
