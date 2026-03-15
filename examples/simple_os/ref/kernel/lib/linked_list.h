/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/lib/linked_list.h -- Index-based intrusive doubly-linked list
 *
 * Mirrors: spl/kernel/lib/linked_list.spl
 */

#ifndef SIMPLE_OS_LINKED_LIST_H
#define SIMPLE_OS_LINKED_LIST_H

#include "common/types.h"
#include "common/config.h"

/* ---- Data structures --------------------------------------------------- */

typedef struct {
    uint32_t prev;     /* Index of previous node, or LIST_NONE */
    uint32_t next;     /* Index of next node, or LIST_NONE     */
    bool     active;   /* Whether this node is currently in a list */
} list_node_t;

typedef struct {
    uint32_t    head;       /* Index of first node, or LIST_NONE */
    uint32_t    tail;       /* Index of last node, or LIST_NONE  */
    uint32_t    len;        /* Number of nodes in the list       */
    uint32_t    capacity;   /* Maximum number of nodes           */
    list_node_t nodes[256]; /* Backing storage for nodes         */
} linked_list_t;

/* ---- API --------------------------------------------------------------- */

/* Create an empty linked list with a given capacity (max 256). */
void linked_list_init(linked_list_t *list, uint32_t capacity);

/* Returns true if the list contains no elements. */
bool linked_list_is_empty(const linked_list_t *list);

/* Returns the number of elements in the list. */
uint32_t linked_list_count(const linked_list_t *list);

/* Push a node index to the back of the list (enqueue). */
void linked_list_push_back(linked_list_t *list, uint32_t index);

/* Push a node index to the front of the list. */
void linked_list_push_front(linked_list_t *list, uint32_t index);

/* Pop and return the front node index. Returns -1 if empty. */
int32_t linked_list_pop_front(linked_list_t *list);

/* Pop and return the back node index. Returns -1 if empty. */
int32_t linked_list_pop_back(linked_list_t *list);

/* Remove a node by index from anywhere in the list. */
void linked_list_remove(linked_list_t *list, uint32_t index);

/* Peek at the front node index without removing it. Returns -1 if empty. */
int32_t linked_list_peek_front(const linked_list_t *list);

/* Peek at the back node index without removing it. Returns -1 if empty. */
int32_t linked_list_peek_back(const linked_list_t *list);

/* Check whether a given node index is currently in the list. */
bool linked_list_contains(const linked_list_t *list, uint32_t index);

#endif /* SIMPLE_OS_LINKED_LIST_H */
