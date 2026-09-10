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

// Generated projection seam. The schema generator replaces this immutable value.
export const GENERATED_KPF_CONTRIBUTIONS: KpfContributionProjection = Object.freeze({
    schemaVersion: 1,
    activationEvents: Object.freeze([
        'onLanguage:simple',
        'onCustomEditor:simple.richSourceEditor',
        'onCommand:simple.richEditor.open',
    ]),
    commands: Object.freeze([
        Object.freeze({
            command: 'simple.lsp.restart',
            title: 'Restart Simple LSP',
            category: 'Simple Language',
            requiredCapability: 'ide.language-session',
        }),
        Object.freeze({
            command: 'simple.lsp.showOutputChannel',
            title: 'Show Simple LSP Output',
            category: 'Simple Language',
        }),
    ]),
});

export function projectContributionCommands(
    projection: KpfContributionProjection,
    admittedCapabilities: ReadonlySet<string>,
): readonly KpfCommandContribution[] {
    return projection.commands.filter((command) => (
        command.requiredCapability === undefined || admittedCapabilities.has(command.requiredCapability)
    ));
}
