#include <stdio.h>
#include <time.h>
#include <gtk/gtk.h>

static long long now_us(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000000LL + ts.tv_nsec / 1000LL;
}

int main(void) {
    long long open_start = now_us();
#if GTK_MAJOR_VERSION >= 4
    if (!gtk_init_check()) {
        puts("gtk_render_status=unavailable");
        puts("gtk_reason=no_display");
        return 0;
    }
#else
    int argc = 0;
    char **argv = NULL;
    if (!gtk_init_check(&argc, &argv)) {
        puts("gtk_render_status=unavailable");
        puts("gtk_reason=no_display");
        return 0;
    }
#endif
    for (int open_i = 0; open_i < 1; open_i++) {
#if GTK_MAJOR_VERSION >= 4
        GtkWidget *open_window = gtk_window_new();
        GtkWidget *open_label = gtk_label_new("Simple GUI");
        gtk_window_set_child(GTK_WINDOW(open_window), open_label);
        g_object_unref(open_window);
#else
        GtkWidget *open_window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
        GtkWidget *open_label = gtk_label_new("Simple GUI");
        gtk_container_add(GTK_CONTAINER(open_window), open_label);
        gtk_widget_destroy(open_window);
#endif
    }
    long long open_elapsed = now_us() - open_start;
    long long start = now_us();
    for (int i = 0; i < 20; i++) {
#if GTK_MAJOR_VERSION >= 4
        GtkWidget *window = gtk_window_new();
        GtkWidget *label = gtk_label_new("Simple GUI");
        gtk_window_set_child(GTK_WINDOW(window), label);
        g_object_unref(window);
#else
        GtkWidget *window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
        GtkWidget *label = gtk_label_new("Simple GUI");
        gtk_container_add(GTK_CONTAINER(window), label);
        gtk_widget_destroy(window);
#endif
    }
    long long elapsed = now_us() - start;
    puts("gtk_render_status=ok");
    printf("gtk_render_iterations=20\n");
    printf("gtk_open_total_us=%lld\n", open_elapsed);
    printf("gtk_widget_total_us=%lld\n", elapsed);
    return 0;
}
