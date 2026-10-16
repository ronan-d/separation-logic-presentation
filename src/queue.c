#include "queue.h"

#include <assert.h>
#include <stdlib.h>

void
init_queue (struct cell **first, struct cell **last)
{
  *first = NULL;
  *last = NULL;
}

void
enqueue (struct queue *q, int n)
{
  struct cell *cell = malloc (sizeof (*cell));

  assert (cell != NULL);

  cell->element = n;
  cell->next = NULL;

  if (q->first == NULL)
    {
      q->first = cell;
    }
  else
    {
      q->last->next = cell;
    }

  q->last = cell;
}

bool
dequeue (struct queue *q, int *n)
{
  if (q->first == NULL)
    {
      return false;
    }

  *n = q->first->element;

  struct cell *new_first = q->first->next;

  free (q->first);

  q->first = new_first;

  return true;
}
