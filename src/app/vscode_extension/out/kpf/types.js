"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.validateAdmission = validateAdmission;
function validateAdmission(metadata) {
    if (!metadata.admitted) {
        throw new Error(`Provider ${metadata.providerId} is not admitted`);
    }
    if (!metadata.providerId || !metadata.generation || !metadata.schemaDigest) {
        throw new Error('Admitted provider metadata is incomplete');
    }
    const capabilityKeys = new Set();
    for (const capability of metadata.capabilities) {
        if (!capability.id || capability.major < 1) {
            throw new Error('Invalid admitted capability');
        }
        const key = `${capability.id}@${capability.major}`;
        if (capabilityKeys.has(key)) {
            throw new Error(`Duplicate admitted capability ${key}`);
        }
        capabilityKeys.add(key);
    }
}
//# sourceMappingURL=types.js.map