#include <stdbool.h>

struct cell {
  int element;
  struct cell *next;
};

struct queue {
  struct cell *first;
  struct cell *next;
};

void enqueue(struct queue *q, int n);

bool dequeue(struct queue *q, int *n);
