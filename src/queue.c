#include "queue.h"

#include <assert.h>
#include <stdlib.h>

void enqueue(struct queue *q, int n) {
  struct cell *cell = malloc(sizeof(*cell));

  assert(cell != NULL);

  cell->element = n;
  cell->next = NULL;

  if (q->first == NULL) {
    q->last = cell;
  }

  q->first = cell;
}

bool dequeue(struct queue *q, int *n) {
  if (q->first == NULL) {
    return false;
  }

  *n = q->first->element;

  struct cell *new_first = q->first->next;

  free(q->first);

  q->first = new_first;

  return true;
}
