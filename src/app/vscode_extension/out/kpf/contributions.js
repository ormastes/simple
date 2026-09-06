"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.GENERATED_KPF_CONTRIBUTIONS = void 0;
exports.projectContributionCommands = projectContributionCommands;
// Generated projection seam. The schema generator replaces this immutable value.
exports.GENERATED_KPF_CONTRIBUTIONS = Object.freeze({
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
function projectContributionCommands(projection, admittedCapabilities) {
    return projection.commands.filter((command) => (command.requiredCapability === undefined || admittedCapabilities.has(command.requiredCapability)));
}
//# sourceMappingURL=contributions.js.map