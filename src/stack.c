struct cell
{
  int element;
  struct cell *next;
};

struct stack
{
  struct cell *first;
};
