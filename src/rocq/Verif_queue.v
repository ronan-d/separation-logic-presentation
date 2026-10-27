Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import queue.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_cell := Tstruct _cell noattr.

Definition t_queue := Tstruct _queue noattr.

Fixpoint queuerep (l: list Z) (first: val) (last: val) : mpred := match l with
| [] => !! (first = nullval) && emp
| n :: [] => !! (first = last) && sepcon
    (malloc_token Ews t_cell first)
    (data_at Ews t_cell (Vint (Int.repr n), nullval) first)
| n :: l' => EX y:val,
    malloc_token Ews t_cell first *
    data_at Ews t_cell (Vint (Int.repr n), y) first *
    queuerep l' y last
end.

Lemma queuerep_cons_cons : forall x y l first last,
  queuerep (x :: y :: l) first last =
    EX p:val,
      malloc_token Ews t_cell first *
      data_at Ews t_cell (Vint (Int.repr x), p) first *
      queuerep (y :: l) p last.
Proof.
  intros.
  reflexivity.
Qed.

Arguments queuerep l first last : simpl never.

Lemma queuerep_local_prop: forall l first last, queuerep l first last |--
  !! (is_pointer_or_null first /\
      (first = nullval <-> l = nil) /\
      (first <> nullval -> is_pointer_or_null last)).
Proof.
  induction l as [| x l' IH]; intros.
  {
    unfold queuerep.
    entailer!.
    split; reflexivity.
  }
  destruct l' as [| x' l'' ].
  {
    unfold queuerep.
    entailer!.
    split.
    - intros.
      subst last.
      inversion H.
    - intros.
      inversion H2.
  }
  rewrite queuerep_cons_cons.
  entailer.
  entailer!.
  split. split.
  - intros.
    subst first.
    inversion H.
  - intros.
    inversion H4.
  - intros.
    destruct (eq_dec p nullval).
    + subst p.
      destruct H2 as [H2 _].
      specialize (H2 (eq_refl _)).
      inversion H2.
    + specialize (H3 n).
      exact H3.
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

Lemma queue_local_prop : forall l p, queue l p |-- !! (isptr p).
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
  destruct l as [| j l' ].
  {
    unfold queuerep.
    forward.
    forward.
    forward.
    forward_call (t_cell, first, gv).
    {
      destruct (eq_dec first nullval); entailer!.
    }
    forward.
    unfold queue.
    entailer.
    Exists nullval.
    Exists last.
    entailer!.
    unfold queuerep.
    entailer!.
  }
  rewrite queuerep_cons_cons.
  Intros p0.
  forward.
  forward.
  forward.
  forward_call (t_cell, first, gv).
  {
    destruct (eq_dec first nullval); entailer!.
  }
  forward.
  unfold queue.
  Exists p0.
  Exists last.
  entailer!.
Qed.

Lemma body_enqueue: semax_body Vprog Gprog f_enqueue enqueue_spec.
Proof.
  start_function.
  forward_call (t_cell, gv).
  Intros vret.
  destruct (eq_dec vret nullval).
  {
    subst vret.
    forward_if (False).
    - forward_call (1).
      entailer.
    - forward.
      entailer.
  }
  forward_if (True).
  {
    forward_call (1).
    entailer.
  }
  {
    forward.
    entailer.
  }
  Intros.
  forward.
  forward.
  forward.
  deadvars!.
  forward_if (
    PROP ()
    LOCAL (temp _cell__1 vret; temp _q p)
    SEP (EX first',
      queuerep (l ++ [i]) first' vret *
      mem_mgr gv *
      malloc_token Ews t_queue p *
      data_at Ews t_queue (first', last) p)
  ).
  {
    subst first.
    forward.
    entailer.
    destruct H6 as [H6 _].
    specialize (H6 (eq_refl _)).
    subst l.
    Exists vret.
    cbn.
    unfold queuerep.
    entailer!.
  }
  {
    deadvars!.
    forward.
    autorewrite with norm.
    focus_SEP 0 3 4.
    apply semax_post' with
      (R' :=
        PROP ()
        LOCAL (temp _t'3 last; temp _cell__1 vret; temp _q p)
        SEP (
          mem_mgr gv;
          malloc_token Ews t_queue p;
          data_at (cs := CompSpecs) Ews t_queue (first, last) p;
          queuerep (l ++ [i]) first vret)).
    {
      Exists first.
      entailer!.
    }
    apply semax_frame'.
    apply semax_frame'.
    apply semax_frame'.
    generalize dependent first.
    induction l as [| x l' IH ].
    {
      intros.
      assert_PROP (False).
      {
        unfold queuerep.
        entailer.
      }
      contradiction.
    }
    destruct l' as [| x' l'' ].
    {
      intros.
      simpl.
      unfold queuerep.
      assert_PROP (first = last).
      {
        entailer.
      }
      subst last.
      Intros.
      forward.
      Exists vret.
      entailer!.
    }
    intros.
    simpl.
    rewrite queuerep_cons_cons with (l := (l'' ++ [i])).
    rewrite queuerep_cons_cons with (l := (l'')).
    Intros p0.
    apply semax_post' with (R' :=
      PROP ()
      LOCAL (temp _t'3 last; temp _cell__1 vret; temp _q p)
      SEP (
        malloc_token Ews t_cell first;
        data_at (cs := CompSpecs) Ews t_cell (Vint (Int.repr x), p0) first;
        queuerep (x' :: l'' ++ [i]) p0 vret)).
    {
      entailer.
      Exists p0.
      entailer!.
    }
    specialize (IH p0).
    assert_PROP (p0 <> nullval).
    {
      entailer!.
      destruct H7 as [H7 _].
      specialize (H7 (eq_refl _)).
      inversion H7.
    }
    specialize (IH H1).
    focus_SEP 2 3.
    apply semax_frame'.
    apply semax_frame'.
    exact IH.
  }
  Intros first'.
  forward.
  entailer!.
  unfold queue.
  Exists first' vret.
  entailer!.
Qed.

Lemma body_new_queue : semax_body Vprog Gprog f_new_queue new_queue_spec.
Proof.
  start_function.
  forward_call (t_queue, gv).
  Intros vret.
  destruct (eq_dec vret nullval).
  {
    subst vret.
    forward_if (False).
    - forward_call (1).
      entailer.
    - exfalso.
      apply H.
      reflexivity.
  }
  forward_if (True).
  {
    exfalso.
    apply n.
    exact H.
  }
  {
    forward.
    entailer!.
  }
  Intros.
  forward.
  forward.
  forward.
  Exists vret.
  entailer!.
  unfold queue.
  Exists nullval nullval.
  entailer!.
  unfold queuerep.
  entailer!.
Qed.
