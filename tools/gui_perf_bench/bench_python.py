#!/usr/bin/env python3
"""GUI Perf Benchmark — Python/tkinter 8K fill + widget render.

Measures: cold startup, warm frame, 8K (7680x4320) fill rate.
Run: python3 bench_python.py [--width 7680 --height 4320 --frames 60]
"""
import sys
import time
import tkinter as tk
import statistics

WIDTH = 7680
HEIGHT = 4320
FRAMES = 60

def parse_args():
    global WIDTH, HEIGHT, FRAMES
    args = sys.argv[1:]
    for i in range(len(args) - 1):
        if args[i] == "--width": WIDTH = int(args[i + 1])
        elif args[i] == "--height": HEIGHT = int(args[i + 1])
        elif args[i] == "--frames": FRAMES = int(args[i + 1])

def main():
    cold_start = time.monotonic()
    parse_args()

    root = tk.Tk()
    root.title("GUI Perf Benchmark - Python/tkinter")
    root.geometry(f"{WIDTH}x{HEIGHT}")

    canvas = tk.Canvas(root, width=WIDTH, height=HEIGHT, bg="#262630", highlightthickness=0)
    canvas.pack(fill=tk.BOTH, expand=True)

    frame_times = []
    frame_count = [0]
    warm_start = [None]

    def draw_frame():
        t0 = time.monotonic()
        if frame_count[0] == 0:
            warm_start[0] = t0

        canvas.delete("bench")

        # Title bar
        canvas.create_rectangle(0, 0, WIDTH, 48, fill="#3366CC", outline="", tags="bench")

        # Sidebar
        canvas.create_rectangle(0, 48, 280, HEIGHT, fill="#1F1F28", outline="", tags="bench")

        # Content text-like rectangles
        for i in range(40):
            w = 400 + (i % 5) * 80
            canvas.create_rectangle(300, 70 + i * 24, 300 + w, 86 + i * 24,
                                    fill="#E5E5E5", outline="", tags="bench")

        # Buttons
        colors = ["#3380CC", "#3D85C6", "#4791BF", "#519CB9",
                  "#5BA8B2", "#66B3AB", "#70BFA5", "#7ACA9E"]
        for i in range(8):
            bx = 300 + (i % 4) * 200
            by = HEIGHT - 200 + (i // 4) * 60
            canvas.create_rectangle(bx, by, bx + 160, by + 40,
                                    fill=colors[i], outline="", tags="bench")

        canvas.update_idletasks()
        t1 = time.monotonic()
        frame_times.append((t1 - t0) * 1000.0)
        frame_count[0] += 1

        if frame_count[0] < FRAMES:
            root.after(1, draw_frame)
        else:
            finish = time.monotonic()
            report(cold_start, warm_start[0], finish, frame_times)
            root.quit()

    def report(cold_t, warm_t, end_t, times):
        n = len(times)
        s = sorted(times)
        p50 = s[n // 2]
        p95 = s[int(n * 0.95)]
        avg = statistics.mean(times)
        cold_ms = (warm_t - cold_t) * 1000.0
        warm_ms = (end_t - warm_t) * 1000.0

        print(f"gui_perf_benchmark_backend=python_tkinter")
        print(f"gui_perf_benchmark_resolution={WIDTH}x{HEIGHT}")
        print(f"gui_perf_benchmark_frames={n}")
        print(f"gui_perf_benchmark_cold_startup_ms={cold_ms:.2f}")
        print(f"gui_perf_benchmark_warm_total_ms={warm_ms:.2f}")
        print(f"gui_perf_benchmark_frame_time_avg_ms={avg:.3f}")
        print(f"gui_perf_benchmark_frame_time_p50_ms={p50:.3f}")
        print(f"gui_perf_benchmark_frame_time_p95_ms={p95:.3f}")
        print(f"gui_perf_benchmark_frame_time_max_ms={s[-1]:.3f}")
        print(f"gui_perf_benchmark_pixel_count={WIDTH * HEIGHT}")
        print(f"gui_perf_benchmark_bytes_per_frame={WIDTH * HEIGHT * 4}")
        print(f"gui_perf_benchmark_status=completed")

    root.after(10, draw_frame)
    root.mainloop()

if __name__ == "__main__":
    main()
