#!/usr/bin/env node
// GUI Perf Benchmark — Node.js headless canvas 8K fill + widget render
// Requires: npm install canvas
// Run: node bench_js_node.js [--width 7680 --height 4320 --frames 60]

const { createCanvas } = require("canvas");
const { performance } = require("perf_hooks");

let W = 7680, H = 4320, FRAMES = 60, FIXTURE = "widgets";
const args = process.argv.slice(2);
for (let i = 0; i < args.length - 1; i++) {
    if (args[i] === "--width") W = parseInt(args[i + 1]);
    if (args[i] === "--height") H = parseInt(args[i + 1]);
    if (args[i] === "--frames") FRAMES = parseInt(args[i + 1]);
    if (args[i] === "--fixture") FIXTURE = args[i + 1];
}

const coldStart = performance.now();
const canvas = createCanvas(W, H);
const ctx = canvas.getContext("2d");
const frameTimes = [];
let warmStart = null;

for (let frame = 0; frame < FRAMES; frame++) {
    const t0 = performance.now();
    if (frame === 0) warmStart = t0;

    ctx.fillStyle = FIXTURE === "gui-perf-cpu-base-solid" ? "#102030" : "#262630";
    ctx.fillRect(0, 0, W, H);

    if (FIXTURE === "gui-perf-cpu-base-solid") {
        const t1 = performance.now();
        frameTimes.push(t1 - t0);
        continue;
    }

    ctx.fillStyle = "#3366CC";
    ctx.fillRect(0, 0, W, 48);

    ctx.fillStyle = "#1F1F28";
    ctx.fillRect(0, 48, 280, H - 48);

    ctx.fillStyle = "#E5E5E5";
    for (let i = 0; i < 40; i++) {
        const w = 400 + (i % 5) * 80;
        ctx.fillRect(300, 70 + i * 24, w, 16);
    }

    const colors = ["#3380CC","#3D85C6","#4791BF","#519CB9",
                     "#5BA8B2","#66B3AB","#70BFA5","#7ACA9E"];
    for (let i = 0; i < 8; i++) {
        ctx.fillStyle = colors[i];
        const bx = 300 + (i % 4) * 200;
        const by = H - 200 + Math.floor(i / 4) * 60;
        ctx.fillRect(bx, by, 160, 40);
    }

    const t1 = performance.now();
    frameTimes.push(t1 - t0);
}

const endTime = performance.now();
const n = frameTimes.length;
const s = [...frameTimes].sort((a, b) => a - b);
const p50 = s[Math.floor(n / 2)];
const p95 = s[Math.floor(n * 0.95)];
const avg = frameTimes.reduce((a, b) => a + b, 0) / n;

// Pixel checksum from final frame
const imgData = ctx.getImageData(0, 0, W, H);
let checksum = 0;
let argbSum32 = 0n;
for (let i = 0; i < imgData.data.length; i += 4) {
    checksum += imgData.data[i] + imgData.data[i+1] + imgData.data[i+2] + imgData.data[i+3];
    argbSum32 += (BigInt(imgData.data[i+3]) << 24n) |
        (BigInt(imgData.data[i]) << 16n) |
        (BigInt(imgData.data[i+1]) << 8n) | BigInt(imgData.data[i+2]);
}

console.log(`gui_perf_benchmark_backend=javascript_node_canvas`);
console.log(`gui_perf_benchmark_resolution=${W}x${H}`);
console.log(`gui_perf_benchmark_frames=${n}`);
console.log(`gui_perf_benchmark_cold_startup_ms=${(warmStart - coldStart).toFixed(2)}`);
console.log(`gui_perf_benchmark_warm_total_ms=${(endTime - warmStart).toFixed(2)}`);
console.log(`gui_perf_benchmark_frame_time_avg_ms=${avg.toFixed(3)}`);
console.log(`gui_perf_benchmark_frame_time_p50_ms=${p50.toFixed(3)}`);
console.log(`gui_perf_benchmark_frame_time_p95_ms=${p95.toFixed(3)}`);
console.log(`gui_perf_benchmark_frame_time_max_ms=${s[n-1].toFixed(3)}`);
console.log(`gui_perf_benchmark_pixel_count=${W * H}`);
console.log(`gui_perf_benchmark_bytes_per_frame=${W * H * 4}`);
console.log(`gui_perf_benchmark_pixel_checksum=${checksum}`);
console.log(`gui_perf_benchmark_argb_sum32=sum32:${argbSum32}`);
console.log(`gui_perf_benchmark_fixture=${FIXTURE}`);
console.log(`gui_perf_benchmark_status=completed`);
