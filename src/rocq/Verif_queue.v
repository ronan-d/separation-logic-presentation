Require Import VST.floyd.proofauto.
Require Import queue.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_cell := Tstruct _cell noattr.

Definition t_queue := Tstruct _queue noattr.

Fixpoint cellrep (l: list val) (first: val) (last: val) : mpred := match sigma with
| x :: l' => EX y:val, data_at Tsh t_cell (x, y) p * cellrep l' y
| [] => !! (p = nullval) && emp
end.

Definition queuerep (l: list val) (queue: val) : mpred := match sigma with
| x :: l' => todo
| [] => !!
end.

Definition new_queue_spec : ident * funspec :=
  DECLARE _new_queue
    POST [ t_queue ]
