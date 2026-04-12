import { type BlockKind, type DetectedBlock } from './blockDetector';
import { simpleToUnicode } from './mathConverter';

export interface MathPreview {
    kind: Extract<BlockKind, 'math' | 'loss' | 'nograd'>;
    indicator: string;
    pretty: string;
    label: string;
    displayText: string;
}

export function isMathLikeBlock(kind: BlockKind): kind is Extract<BlockKind, 'math' | 'loss' | 'nograd'> {
    return kind === 'math' || kind === 'loss' || kind === 'nograd';
}

export function indicatorForMathKind(kind: Extract<BlockKind, 'math' | 'loss' | 'nograd'>): string {
    switch (kind) {
        case 'loss':
            return '\u2112';
        case 'nograd':
            return '\u2205';
        default:
            return '\u2202';
    }
}

export function labelForMathKind(kind: Extract<BlockKind, 'math' | 'loss' | 'nograd'>): string {
    switch (kind) {
        case 'loss':
            return 'loss{}';
        case 'nograd':
            return 'nograd{}';
        default:
            return 'm{}';
    }
}

export function buildMathPreview(block: Pick<DetectedBlock, 'kind' | 'content'>): MathPreview | undefined {
    if (!isMathLikeBlock(block.kind)) {
        return undefined;
    }
    const indicator = indicatorForMathKind(block.kind);
    const pretty = simpleToUnicode(block.content);
    return {
        kind: block.kind,
        indicator,
        pretty,
        label: labelForMathKind(block.kind),
        displayText: `${indicator}{${pretty}}`,
    };
}
