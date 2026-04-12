"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.SimpleFoldingRangeProvider = void 0;
const simpleAnalysisIndex_1 = require("./analysis/simpleAnalysisIndex");
class SimpleFoldingRangeProvider {
    provideFoldingRanges(document) {
        return (0, simpleAnalysisIndex_1.collectFoldingRanges)(document);
    }
}
exports.SimpleFoldingRangeProvider = SimpleFoldingRangeProvider;
//# sourceMappingURL=nativeFoldingProvider.js.map