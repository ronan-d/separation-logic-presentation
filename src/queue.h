#include <stdbool.h>

struct queue;

struct queue *new_queue (void);

void enqueue (struct queue *q, int n);

bool dequeue (struct queue *q, int *n);
