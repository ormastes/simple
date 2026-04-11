"use strict";
/**
 * Rich editor module barrel — activation entry point.
 */
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.activateRichEditorFeatures = activateRichEditorFeatures;
const vscode = __importStar(require("vscode"));
const richCustomEditor_1 = require("./richCustomEditor");
function activateRichEditorFeatures(context) {
    context.subscriptions.push(vscode.window.registerCustomEditorProvider(richCustomEditor_1.RichCustomEditorProvider.viewType, new richCustomEditor_1.RichCustomEditorProvider(context.extensionUri), {
        webviewOptions: { retainContextWhenHidden: true },
        supportsMultipleEditorsPerDocument: false,
    }));
    context.subscriptions.push(vscode.commands.registerCommand('simple.richEditor.open', () => {
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            void vscode.commands.executeCommand('vscode.openWith', editor.document.uri, richCustomEditor_1.RichCustomEditorProvider.viewType);
        }
    }));
}
//# sourceMappingURL=index.js.map