// GUI Perf Benchmark — C/GTK3 8K fill + widget render
// Measures: cold startup, warm frame, 8K (7680x4320) fill rate
// Build: gcc -O2 $(pkg-config --cflags --libs gtk+-3.0) -o bench_gtk bench_gtk.c
// Run:   ./bench_gtk [--width 7680 --height 4320 --frames 60]

#include <gtk/gtk.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int g_width = 7680;
static int g_height = 4320;
static int g_frames = 60;
static int g_frame_count = 0;
static double g_frame_times[4096];
static struct timespec g_start, g_warm_start;

static double elapsed_ms(struct timespec *a, struct timespec *b) {
    return (b->tv_sec - a->tv_sec) * 1000.0 +
           (b->tv_nsec - a->tv_nsec) / 1e6;
}

static unsigned long pixel_checksum(unsigned char *data, int w, int h, int stride) {
    unsigned long sum = 0;
    for (int y = 0; y < h; y++) {
        unsigned char *row = data + y * stride;
        for (int x = 0; x < w * 4; x += 4) {
            sum += row[x] + row[x+1] + row[x+2] + row[x+3];
        }
    }
    return sum;
}

static gboolean on_draw(GtkWidget *widget, cairo_t *cr, gpointer data) {
    struct timespec frame_start, frame_end;
    clock_gettime(CLOCK_MONOTONIC, &frame_start);

    if (g_frame_count == 0) {
        g_warm_start = frame_start;
    }

    // Fill background — 8K pixel work
    cairo_set_source_rgb(cr, 0.15, 0.15, 0.20);
    cairo_paint(cr);

    // Draw representative GUI widgets
    // Title bar
    cairo_set_source_rgb(cr, 0.2, 0.4, 0.8);
    cairo_rectangle(cr, 0, 0, g_width, 48);
    cairo_fill(cr);

    // Sidebar
    cairo_set_source_rgb(cr, 0.12, 0.12, 0.16);
    cairo_rectangle(cr, 0, 48, 280, g_height - 48);
    cairo_fill(cr);

    // Content area with text-like rectangles
    cairo_set_source_rgb(cr, 0.9, 0.9, 0.9);
    for (int i = 0; i < 40; i++) {
        cairo_rectangle(cr, 300, 70 + i * 24, 400 + (i % 5) * 80, 16);
        cairo_fill(cr);
    }

    // Buttons
    for (int i = 0; i < 8; i++) {
        cairo_set_source_rgb(cr, 0.2 + i * 0.05, 0.5, 0.8 - i * 0.05);
        double bx = 300 + (i % 4) * 200;
        double by = g_height - 200 + (i / 4) * 60;
        cairo_rectangle(cr, bx, by, 160, 40);
        cairo_fill(cr);
    }

    clock_gettime(CLOCK_MONOTONIC, &frame_end);

    if (g_frame_count < 4096) {
        g_frame_times[g_frame_count] = elapsed_ms(&frame_start, &frame_end);
    }
    g_frame_count++;

    if (g_frame_count < g_frames) {
        gtk_widget_queue_draw(widget);
    } else {
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC, &now);

        // Compute stats
        double total_frame = 0;
        double max_frame = 0;
        int n = g_frame_count < 4096 ? g_frame_count : 4096;
        double sorted[4096];
        memcpy(sorted, g_frame_times, n * sizeof(double));
        for (int i = 0; i < n - 1; i++)
            for (int j = i + 1; j < n; j++)
                if (sorted[i] > sorted[j]) {
                    double t = sorted[i]; sorted[i] = sorted[j]; sorted[j] = t;
                }
        for (int i = 0; i < n; i++) total_frame += sorted[i];

        double cold_ms = elapsed_ms(&g_start, &g_warm_start);
        double warm_ms = elapsed_ms(&g_warm_start, &now);
        double p50 = sorted[n / 2];
        double p95 = sorted[(int)(n * 0.95)];
        double avg = total_frame / n;

        printf("gui_perf_benchmark_backend=gtk3\n");
        printf("gui_perf_benchmark_resolution=%dx%d\n", g_width, g_height);
        printf("gui_perf_benchmark_frames=%d\n", g_frame_count);
        printf("gui_perf_benchmark_cold_startup_ms=%.2f\n", cold_ms);
        printf("gui_perf_benchmark_warm_total_ms=%.2f\n", warm_ms);
        printf("gui_perf_benchmark_frame_time_avg_ms=%.3f\n", avg);
        printf("gui_perf_benchmark_frame_time_p50_ms=%.3f\n", p50);
        printf("gui_perf_benchmark_frame_time_p95_ms=%.3f\n", p95);
        printf("gui_perf_benchmark_frame_time_max_ms=%.3f\n", sorted[n - 1]);
        printf("gui_perf_benchmark_pixel_count=%ld\n", (long)g_width * g_height);
        printf("gui_perf_benchmark_bytes_per_frame=%ld\n", (long)g_width * g_height * 4);
        printf("gui_perf_benchmark_status=completed\n");

        gtk_main_quit();
    }
    return FALSE;
}

int main(int argc, char *argv[]) {
    clock_gettime(CLOCK_MONOTONIC, &g_start);

    for (int i = 1; i < argc - 1; i++) {
        if (strcmp(argv[i], "--width") == 0) g_width = atoi(argv[i+1]);
        if (strcmp(argv[i], "--height") == 0) g_height = atoi(argv[i+1]);
        if (strcmp(argv[i], "--frames") == 0) g_frames = atoi(argv[i+1]);
    }

    gtk_init(&argc, &argv);

    GtkWidget *window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_default_size(GTK_WINDOW(window), g_width, g_height);
    gtk_window_set_title(GTK_WINDOW(window), "GUI Perf Benchmark - GTK3");
    g_signal_connect(window, "destroy", G_CALLBACK(gtk_main_quit), NULL);

    GtkWidget *drawing = gtk_drawing_area_new();
    gtk_container_add(GTK_CONTAINER(window), drawing);
    g_signal_connect(drawing, "draw", G_CALLBACK(on_draw), NULL);

    gtk_widget_show_all(window);
    gtk_main();

    return 0;
}
