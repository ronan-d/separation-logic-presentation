Require Import VST.floyd.proofauto.
Require Import queue.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_cell := Tstruct _cell noattr.

Definition t_queue := Tstruct _queue noattr.

Fixpoint queuerep (l: list val) (first: val) (last: val) : mpred := match l with
| x :: l' => EX y:val, data_at Tsh t_cell (x, y) first * queuerep l' y last
| [] => !! (first = nullval) && emp
end.

Definition new_queue_spec : ident * funspec :=
  DECLARE _new_queue
  WITH first: val, last: val
  PRE [tptr (tptr t_cell), tptr (tptr t_cell)]
    PROP ()
    PARAMS (first; last)
