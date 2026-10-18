#include <stdbool.h>

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

struct queue new_queue (void);

void init_queue (struct cell **first, struct cell **last);

void enqueue (struct queue *q, int n);

bool dequeue (struct queue *q, int *n);
