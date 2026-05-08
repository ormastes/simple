#!/usr/bin/env node

const fs = require('fs');
const zlib = require('zlib');

const [pngPath, ppmPath, widthArg, heightArg] = process.argv.slice(2);
if (!pngPath || !ppmPath || !widthArg || !heightArg) {
    console.error('Usage: node png_to_ppm.js <input.png> <output.ppm> <width> <height>');
    process.exit(2);
}

const targetWidth = Number(widthArg);
const targetHeight = Number(heightArg);

function paethPredictor(a, b, c) {
    const p = a + b - c;
    const pa = Math.abs(p - a);
    const pb = Math.abs(p - b);
    const pc = Math.abs(p - c);
    if (pa <= pb && pa <= pc) return a;
    if (pb <= pc) return b;
    return c;
}

function decodePng(buffer) {
    if (buffer.slice(0, 8).toString('hex') !== '89504e470d0a1a0a') {
        throw new Error('input is not a PNG');
    }
    let offset = 8;
    let width = 0;
    let height = 0;
    let colorType = 0;
    let bitDepth = 0;
    const idat = [];
    while (offset < buffer.length) {
        const length = buffer.readUInt32BE(offset); offset += 4;
        const type = buffer.slice(offset, offset + 4).toString('ascii'); offset += 4;
        const data = buffer.slice(offset, offset + length); offset += length;
        offset += 4;
        if (type === 'IHDR') {
            width = data.readUInt32BE(0);
            height = data.readUInt32BE(4);
            bitDepth = data[8];
            colorType = data[9];
            if (data[12] !== 0) throw new Error('interlaced PNG screenshots are not supported');
        } else if (type === 'IDAT') {
            idat.push(data);
        } else if (type === 'IEND') {
            break;
        }
    }
    if (bitDepth !== 8 || (colorType !== 2 && colorType !== 6)) {
        throw new Error(`unsupported PNG format bitDepth=${bitDepth} colorType=${colorType}`);
    }
    const channels = colorType === 6 ? 4 : 3;
    const stride = width * channels;
    const inflated = zlib.inflateSync(Buffer.concat(idat));
    const raw = Buffer.alloc(stride * height);
    let src = 0;
    for (let y = 0; y < height; y++) {
        const filter = inflated[src++];
        const rowOffset = y * stride;
        const prevOffset = rowOffset - stride;
        for (let x = 0; x < stride; x++) {
            const left = x >= channels ? raw[rowOffset + x - channels] : 0;
            const up = y > 0 ? raw[prevOffset + x] : 0;
            const upLeft = y > 0 && x >= channels ? raw[prevOffset + x - channels] : 0;
            const value = inflated[src++];
            if (filter === 0) raw[rowOffset + x] = value;
            else if (filter === 1) raw[rowOffset + x] = (value + left) & 255;
            else if (filter === 2) raw[rowOffset + x] = (value + up) & 255;
            else if (filter === 3) raw[rowOffset + x] = (value + Math.floor((left + up) / 2)) & 255;
            else if (filter === 4) raw[rowOffset + x] = (value + paethPredictor(left, up, upLeft)) & 255;
            else throw new Error(`unsupported PNG filter ${filter}`);
        }
    }
    const rgb = Buffer.alloc(width * height * 3);
    for (let i = 0, j = 0; i < raw.length; i += channels, j += 3) {
        rgb[j] = raw[i];
        rgb[j + 1] = raw[i + 1];
        rgb[j + 2] = raw[i + 2];
    }
    return { width, height, rgb };
}

function cropRgb(image, width, height) {
    if (image.width < width || image.height < height) {
        throw new Error(`PNG screenshot too small: ${image.width}x${image.height}`);
    }
    if (image.width === width && image.height === height) return image.rgb;
    const out = Buffer.alloc(width * height * 3);
    for (let y = 0; y < height; y++) {
        image.rgb.copy(out, y * width * 3, y * image.width * 3, y * image.width * 3 + width * 3);
    }
    return out;
}

try {
    const image = decodePng(fs.readFileSync(pngPath));
    const rgb = cropRgb(image, targetWidth, targetHeight);
    fs.writeFileSync(ppmPath, Buffer.concat([
        Buffer.from(`P6\n${targetWidth} ${targetHeight}\n255\n`, 'ascii'),
        rgb
    ]));
} catch (err) {
    console.error(err.stack || err.message || err);
    process.exit(1);
}
