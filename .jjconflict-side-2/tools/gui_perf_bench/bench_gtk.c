// GUI Perf Benchmark — C/GTK3 8K fill + widget render
// Measures: cold startup, warm frame, 8K (7680x4320) fill rate
// Build: gcc -O2 $(pkg-config --cflags --libs gtk+-3.0) -o bench_gtk bench_gtk.c
// Run:   ./bench_gtk [--width 7680 --height 4320 --frames 60]

#include <gtk/gtk.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int g_width = 7680;
static int g_height = 4320;
static int g_frames = 60;
static int g_frame_count = 0;
static int g_solid_fixture = 0;
static cairo_surface_t *g_surface = NULL;
static double g_frame_times[4096];
static double g_draw_times[4096];
static struct timespec g_start, g_warm_start, g_prev_frame_start;

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
    cairo_t *surface_cr = NULL;
    if (g_solid_fixture) {
        surface_cr = cairo_create(g_surface);
        cr = surface_cr;
    }
    struct timespec frame_start, frame_end;
    clock_gettime(CLOCK_MONOTONIC, &frame_start);

    if (g_frame_count == 0) {
        g_warm_start = frame_start;
    }

    // Fill background — 8K pixel work
    if (g_solid_fixture)
        cairo_set_source_rgb(cr, 16.0 / 255.0, 32.0 / 255.0, 48.0 / 255.0);
    else
        cairo_set_source_rgb(cr, 0.15, 0.15, 0.20);
    cairo_paint(cr);

    if (g_solid_fixture) {
        goto draw_complete;
    }

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

draw_complete:
    if (surface_cr != NULL) cairo_destroy(surface_cr);
    clock_gettime(CLOCK_MONOTONIC, &frame_end);

    if (g_frame_count < 4096) {
        g_draw_times[g_frame_count] = elapsed_ms(&frame_start, &frame_end);
        if (g_frame_count > 0) {
            g_frame_times[g_frame_count - 1] = elapsed_ms(&g_prev_frame_start, &frame_start);
        }
    }
    g_prev_frame_start = frame_start;
    g_frame_count++;

    if (g_frame_count < g_frames) {
        gtk_widget_queue_draw(widget);
    } else {
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC, &now);

        // Frame-to-frame interval stats (full render-present cycle)
        int nf = g_frame_count > 1 ? g_frame_count - 1 : 0;
        if (nf > 4096) nf = 4096;
        double sorted[4096];
        memcpy(sorted, g_frame_times, nf * sizeof(double));
        for (int i = 0; i < nf - 1; i++)
            for (int j = i + 1; j < nf; j++)
                if (sorted[i] > sorted[j]) {
                    double t = sorted[i]; sorted[i] = sorted[j]; sorted[j] = t;
                }
        double total_frame = 0;
        for (int i = 0; i < nf; i++) total_frame += sorted[i];

        // Draw-only stats (cairo calls only, for reference)
        int nd = g_frame_count < 4096 ? g_frame_count : 4096;
        double draw_sorted[4096];
        memcpy(draw_sorted, g_draw_times, nd * sizeof(double));
        for (int i = 0; i < nd - 1; i++)
            for (int j = i + 1; j < nd; j++)
                if (draw_sorted[i] > draw_sorted[j]) {
                    double t = draw_sorted[i]; draw_sorted[i] = draw_sorted[j]; draw_sorted[j] = t;
                }

        double cold_ms = elapsed_ms(&g_start, &g_warm_start);
        double warm_ms = elapsed_ms(&g_warm_start, &now);
        double p50 = nf > 0 ? sorted[nf / 2] : 0;
        double p95 = nf > 0 ? sorted[(int)(nf * 0.95)] : 0;
        double avg = nf > 0 ? total_frame / nf : 0;

        printf("gui_perf_benchmark_backend=gtk3\n");
        printf("gui_perf_benchmark_resolution=%dx%d\n", g_width, g_height);
        printf("gui_perf_benchmark_frames=%d\n", g_frame_count);
        printf("gui_perf_benchmark_cold_startup_ms=%.2f\n", cold_ms);
        printf("gui_perf_benchmark_warm_total_ms=%.2f\n", warm_ms);
        printf("gui_perf_benchmark_frame_time_avg_ms=%.3f\n", avg);
        printf("gui_perf_benchmark_frame_time_p50_ms=%.3f\n", p50);
        printf("gui_perf_benchmark_frame_time_p95_ms=%.3f\n", p95);
        printf("gui_perf_benchmark_frame_time_max_ms=%.3f\n", nf > 0 ? sorted[nf - 1] : 0);
        printf("gui_perf_benchmark_draw_only_avg_ms=%.3f\n", nd > 0 ? draw_sorted[nd / 2] : 0);
        printf("gui_perf_benchmark_pixel_count=%ld\n", (long)g_width * g_height);
        printf("gui_perf_benchmark_bytes_per_frame=%ld\n", (long)g_width * g_height * 4);
        if (g_solid_fixture) {
            unsigned long long argb_sum32 = 0;
            cairo_surface_flush(g_surface);
            unsigned char *pixels = cairo_image_surface_get_data(g_surface);
            int stride = cairo_image_surface_get_stride(g_surface);
            for (int y = 0; y < g_height; y++) {
                uint32_t *row = (uint32_t *)(pixels + y * stride);
                for (int x = 0; x < g_width; x++) argb_sum32 += row[x];
            }
            printf("gui_perf_benchmark_argb_sum32=sum32:%llu\n", argb_sum32);
        }
        printf("gui_perf_benchmark_fixture=%s\n", g_solid_fixture ? "gui-perf-cpu-base-solid" : "widgets");
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
        if (strcmp(argv[i], "--fixture") == 0) g_solid_fixture = strcmp(argv[i+1], "gui-perf-cpu-base-solid") == 0;
    }

    gtk_init(&argc, &argv);
    if (g_solid_fixture) {
        g_surface = cairo_image_surface_create(CAIRO_FORMAT_ARGB32, g_width, g_height);
    }

    GtkWidget *window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_default_size(GTK_WINDOW(window), g_width, g_height);
    gtk_window_set_title(GTK_WINDOW(window), "GUI Perf Benchmark - GTK3");
    g_signal_connect(window, "destroy", G_CALLBACK(gtk_main_quit), NULL);

    GtkWidget *drawing = gtk_drawing_area_new();
    gtk_container_add(GTK_CONTAINER(window), drawing);
    g_signal_connect(drawing, "draw", G_CALLBACK(on_draw), NULL);

    gtk_widget_show_all(window);
    gtk_main();
    if (g_surface != NULL) cairo_surface_destroy(g_surface);

    return 0;
}
