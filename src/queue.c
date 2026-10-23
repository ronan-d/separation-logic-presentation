#include "queue.h"

#include <stdlib.h>

struct cell
{
  int element;
  struct cell *next;
};

struct queue
{
  struct cell *first;
  struct cell *last;
};

struct queue *
new_queue (void)
{
  struct queue *p = malloc (sizeof (*p));

  if (!p)
    exit (1);

  p->first = NULL;
  p->last = NULL;

  return p;
}

void
enqueue (struct queue *q, int n)
{
  struct cell *cell = malloc (sizeof (*cell));

  if (!cell)
    exit (1);

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

int
dequeue (struct queue *q)
{
  struct cell *c = q->first;

  int res = c->element;
  q->first = c->next;

  free (c);

  return res;
}
