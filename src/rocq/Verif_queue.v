Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import queue.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_cell := Tstruct _cell noattr.

Definition t_queue := Tstruct _queue noattr.

Fixpoint queuerep (l: list Z) (first: val) (last: val) : mpred := match l with
| n :: _ :: l' => EX y:val,
    malloc_token Ews t_cell first *
    data_at Ews t_cell (Vint (Int.repr n), y) first *
    queuerep l' y last
| n :: [] => !! (first = last) && sepcon
    (malloc_token Ews t_cell first)
    (data_at Ews t_cell (Vint (Int.repr n), nullval) first)
| [] => !! (first = nullval) && emp
end.

Arguments queuerep l first last : simpl never.

Lemma queuerep_local_prop: forall l first last, queuerep l first last |--
  !! (is_pointer_or_null first /\ (first=nullval <-> l=nil)).
Proof.
  intros.
  revert first last.
  induction l as [| x l' IH ]; intros.
  {
    unfold queuerep.
    entailer!.
    split; auto.
  }
  unfold queuerep. fold queuerep.
  destruct l' as [| x' l''].
  {
    entailer!.
    split; intros.
    - subst last.
      eapply field_compatible_nullval.
      exact H0.
    - inversion H2.
  }
  entailer.
  entailer!.
  split; intros.
  - subst first.
    eapply field_compatible_nullval.
    exact H0.
  - inversion H2.
Qed.

#[export] Hint Resolve queuerep_local_prop : saturate_local.

Lemma queuerep_first_valid_pointer: forall l first last,
  queuerep l first last |-- valid_pointer first.
Proof.
  intros.
  unfold queuerep.
  destruct l; cbn.
  - entailer!.
  - destruct l; cbn.
    + entailer!.
    + Intros y.
      auto with valid_pointer.
Qed.

#[export] Hint Resolve queuerep_first_valid_pointer : valid_pointer.

Definition queue (l : list Z) (p: val) :=
  EX first last: val,
    malloc_token Ews t_queue p *
    data_at Ews t_queue (first, last) p *
    queuerep l first last.

Lemma queue_local_prop : forall l p, queue l p |-- !! (isptr p ).
Proof.
  intros.
  unfold queue.
  entailer.
  entailer!.
Qed.

#[export] Hint Resolve queue_local_prop : saturate_local.

Lemma queue_valid_pointer: forall l p,
  queue l p |-- valid_pointer p.
Proof.
  intros.
  unfold queue.
  entailer.
Qed.

Definition new_queue_spec : ident * funspec :=
  DECLARE _new_queue
  WITH gv: globals
  PRE [ ]
    PROP () PARAMS() GLOBALS(gv) SEP (mem_mgr gv)
  POST [ tptr t_queue ]
    EX p: val, PROP ( ) RETURN (p) SEP (queue nil p; mem_mgr gv).

Definition enqueue_spec : ident * funspec :=
  DECLARE _enqueue
  WITH p: val, i: Z, l: list Z, gv: globals
  PRE [ tptr t_queue, tint ]
    PROP (Int.min_signed <= i <= Int.max_signed)
    PARAMS (p; Vint (Int.repr i)) GLOBALS(gv)
    SEP (queue l p; mem_mgr gv)
  POST [ tvoid ]
    PROP ( ) RETURN () SEP (queue (l ++ [i]) p; mem_mgr gv).

Definition dequeue_spec : ident * funspec :=
  DECLARE _dequeue
  WITH p: val, i: Z, l: list Z, gv: globals
  PRE [ tptr t_queue ]
    PROP ()
    PARAMS (p) GLOBALS(gv)
    SEP (queue (i :: l) p; mem_mgr gv)
  POST [ tint ]
    PROP ( ) RETURN (Vint (Int.repr i)) SEP (queue l p; mem_mgr gv).

 Definition Gprog : funspecs :=
        ltac:(with_library prog [
                   new_queue_spec; enqueue_spec; dequeue_spec
 ]).

Lemma body_dequeue: semax_body Vprog Gprog f_dequeue dequeue_spec.
Proof.
  start_function.
  forward.
  destruct l.
  - unfold queuerep.
    forward.
    forward.
    forward.
    deadvars!.
    forward_call (t_cell, first, gv).
    + entailer.
