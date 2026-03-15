/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/lib/linked_list.c -- Index-based intrusive doubly-linked list
 *
 * Mirrors: spl/kernel/lib/linked_list.spl
 */

#include "kernel/lib/linked_list.h"

/* ------------------------------------------------------------------------ */

void linked_list_init(linked_list_t *list, uint32_t capacity)
{
    uint32_t cap = capacity > 256 ? 256 : capacity;

    list->head     = LIST_NONE;
    list->tail     = LIST_NONE;
    list->len      = 0;
    list->capacity = cap;

    for (uint32_t i = 0; i < 256; i++) {
        list->nodes[i].prev   = LIST_NONE;
        list->nodes[i].next   = LIST_NONE;
        list->nodes[i].active = false;
    }
}

/* ------------------------------------------------------------------------ */

bool linked_list_is_empty(const linked_list_t *list)
{
    return list->len == 0;
}

/* ------------------------------------------------------------------------ */

uint32_t linked_list_count(const linked_list_t *list)
{
    return list->len;
}

/* ------------------------------------------------------------------------ */

void linked_list_push_back(linked_list_t *list, uint32_t index)
{
    if (index >= list->capacity) {
        return;
    }
    if (list->nodes[index].active) {
        return; /* Already in list -- avoid corruption */
    }

    list->nodes[index].prev   = list->tail;
    list->nodes[index].next   = LIST_NONE;
    list->nodes[index].active = true;

    if (list->tail != LIST_NONE) {
        list->nodes[list->tail].next = index;
    } else {
        /* List was empty -- this node is also the head. */
        list->head = index;
    }

    list->tail = index;
    list->len++;
}

/* ------------------------------------------------------------------------ */

void linked_list_push_front(linked_list_t *list, uint32_t index)
{
    if (index >= list->capacity) {
        return;
    }
    if (list->nodes[index].active) {
        return;
    }

    list->nodes[index].prev   = LIST_NONE;
    list->nodes[index].next   = list->head;
    list->nodes[index].active = true;

    if (list->head != LIST_NONE) {
        list->nodes[list->head].prev = index;
    } else {
        list->tail = index;
    }

    list->head = index;
    list->len++;
}

/* ------------------------------------------------------------------------ */

int32_t linked_list_pop_front(linked_list_t *list)
{
    if (list->head == LIST_NONE) {
        return -1;
    }

    uint32_t index = list->head;
    uint32_t next  = list->nodes[index].next;

    if (next != LIST_NONE) {
        list->nodes[next].prev = LIST_NONE;
    } else {
        /* List is now empty. */
        list->tail = LIST_NONE;
    }

    list->head = next;
    list->nodes[index].prev   = LIST_NONE;
    list->nodes[index].next   = LIST_NONE;
    list->nodes[index].active = false;
    list->len--;

    return (int32_t)index;
}

/* ------------------------------------------------------------------------ */

int32_t linked_list_pop_back(linked_list_t *list)
{
    if (list->tail == LIST_NONE) {
        return -1;
    }

    uint32_t index = list->tail;
    uint32_t prev  = list->nodes[index].prev;

    if (prev != LIST_NONE) {
        list->nodes[prev].next = LIST_NONE;
    } else {
        list->head = LIST_NONE;
    }

    list->tail = prev;
    list->nodes[index].prev   = LIST_NONE;
    list->nodes[index].next   = LIST_NONE;
    list->nodes[index].active = false;
    list->len--;

    return (int32_t)index;
}

/* ------------------------------------------------------------------------ */

void linked_list_remove(linked_list_t *list, uint32_t index)
{
    if (index >= list->capacity) {
        return;
    }
    if (!list->nodes[index].active) {
        return;
    }

    uint32_t prev = list->nodes[index].prev;
    uint32_t next = list->nodes[index].next;

    /* Patch the previous node's next pointer (or update head). */
    if (prev != LIST_NONE) {
        list->nodes[prev].next = next;
    } else {
        list->head = next;
    }

    /* Patch the next node's prev pointer (or update tail). */
    if (next != LIST_NONE) {
        list->nodes[next].prev = prev;
    } else {
        list->tail = prev;
    }

    list->nodes[index].prev   = LIST_NONE;
    list->nodes[index].next   = LIST_NONE;
    list->nodes[index].active = false;
    list->len--;
}

/* ------------------------------------------------------------------------ */

int32_t linked_list_peek_front(const linked_list_t *list)
{
    if (list->head == LIST_NONE) {
        return -1;
    }
    return (int32_t)list->head;
}

/* ------------------------------------------------------------------------ */

int32_t linked_list_peek_back(const linked_list_t *list)
{
    if (list->tail == LIST_NONE) {
        return -1;
    }
    return (int32_t)list->tail;
}

/* ------------------------------------------------------------------------ */

bool linked_list_contains(const linked_list_t *list, uint32_t index)
{
    if (index >= list->capacity) {
        return false;
    }
    return list->nodes[index].active;
}
