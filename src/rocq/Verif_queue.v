Require Import VST.floyd.proofauto.
Require Import queue.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_cell := Tstruct _cell noattr.

Definition t_queue := Tstruct _queue noattr.

Fixpoint queuerep (l: list val) (first: val) (last: val) : mpred := match l with
| x :: _ :: l' => EX y:val, data_at Tsh t_cell (x, y) first * queuerep l' y last
| x :: [] => !! (first = last) && emp
| [] => !! (first = nullval) && emp
end.

Definition new_queue_spec : ident * funspec :=
  DECLARE _new_queue
  WITH gv: globals
  PRE [ ]
    PROP () PARAMS() GLOBALS(gv) SEP (mem_mgr gv)
  POST [ tptr t_queue ]
    EX p: val, PROP ( ) RETURN (p) SEP (queuerep nil )
