struct cell {
  int element;
  struct cell *next;
};

struct queue {
  struct cell *first;
  struct cell *next;
};
