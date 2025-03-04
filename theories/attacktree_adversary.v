Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attacktree.

Section AdversarySets. 
    Context {components : Type}.
    
(** pi 
 ** 
 ** The set of adversary events in an attack tree. *)

    Fixpoint piHelper {A : attacktree components} (edges : edgesT A) : 
        list (eventT A) :=
    match edges with
    | (ev1, ev2) :: edges' => match (myLabel A ev1), (myLabel A ev2) with
                              | inr _, inr _ => ev1 :: ev2 :: (piHelper edges')
                              | inr _, inl _ => ev1 :: (piHelper edges')
                              | inl _, inr _ => ev2 :: (piHelper edges')
                              | inl _, inl _ => piHelper edges'
                              end
    | nil => nil
    end.

    Definition pi (A : attacktree components) : 
        list (eventT A) :=
    piHelper (myEdges A).

    Hint Unfold pi : core.

    Lemma pi_fact : forall A ev,
        In ev (pi A)
        <->
        (exists ev', In (ev, ev') (myEdges A) \/ In (ev', ev) (myEdges A)) 
         /\ 
        (exists adv, myLabel A ev = inr adv).
    Proof.
        intros A ev; autounfold; split; intros H.
        - split; induction (myEdges A); try (inversion H; fail);
          destruct a as [ev1 ev2]; simpl in H;
          remember (myLabel A ev1) as Hl1; remember (myLabel A ev2) as Hl2;
          destruct Hl1, Hl2;
          try (repeat destruct H; subst);
          try (apply IHl in H; destruct H as [ans H]; exists ans; simpl; destruct H; auto);
          try (exists ev1; simpl; auto; fail);
          try (exists ev2; simpl; auto; fail);
          try (exists a; auto; fail);
          try (exists a0; auto; fail).
        - destruct H as [HIn HAdv]; destruct HIn as [ev' HIn]; destruct HAdv as [adv HAdv];
          induction (myEdges A); try (destruct HIn as [HIn|HIn]; inversion HIn; fail);
          destruct a as [ev1 ev2]; destruct HIn; simpl; destruct H;
          try (inversion H; destruct (myLabel A ev); destruct (myLabel A ev'); try (inversion HAdv; fail); simpl; auto);
          try (destruct (myLabel A ev1); destruct (myLabel A ev2); repeat right; apply IHl; auto).
    Qed.


(** tau
 ** 
 ** The set of time-constrained adversary events in an attack tree. *)

Fixpoint tau_helper {A : attacktree components} (edges : edgesT A) :
    list (eventT A) :=
match edges with
| (ev1, ev2) :: edges' => match (myLabel A ev1), (myLabel A ev2) with
                 | inl _, inr _ => ev2 :: (tau_helper edges')
                 | _, _ => tau_helper edges'
                 end
| nil => nil
end.

Definition tau (A : attacktree components) : 
    list (eventT A) :=
tau_helper (myEdges A).

Hint Unfold tau : core.

Lemma tau_fact : forall A ev,
    In ev (tau A)
    <->
    (exists ev' meas, In (ev', ev) (myEdges A) /\ myLabel A ev' = inl meas) 
    /\ 
    (exists adv, myLabel A ev = inr adv).
Proof.
    intros A ev; autounfold; split; intros H.
    - split; induction (myEdges A); try (inversion H; fail);
      destruct a as [ev1 ev2]; simpl in H;
      remember (myLabel A ev1) as Hl1; remember (myLabel A ev2) as Hl2;
      destruct Hl1, Hl2;
      try (destruct H; subst);
      try (apply IHl in H; destruct H as [ans H]; exists ans; auto);
      try (destruct H as [ans' H]; destruct H; exists ans'; simpl; auto).
    -- exists ev1, m; simpl; auto.
    -- exists a; auto.
    - destruct H as [HIn HAdv]; destruct HIn as [ev' HIn]; destruct HIn as [meas HIn];
      destruct HIn as [HIn HMeas]; destruct HAdv as [adv HAdv];
      induction (myEdges A); try (inversion HIn; fail).
      destruct a as [ev1 ev2]; destruct HIn; simpl.
    -- inversion H; destruct (myLabel A ev'); destruct (myLabel A ev); inversion HAdv; inversion HMeas; simpl; auto.
    -- destruct (myLabel A ev1); destruct (myLabel A ev2); repeat right; apply IHl; auto.
Qed.


(*
(** Tau is a subset of Pi. *)
Lemma tau_pi' : forall A,
mIncluded_fix (myEqDec_event A) (tau A) (pi A).
Proof.
unfold pi, tau; unfold mIncluded_fix; intros A. induction (myEdges A).
- simpl. auto.
- destruct a as [ev1 ev2]. simpl. 
destruct (myLabel A ev1), (myLabel A ev2).
-- auto.
--
Abort.

Lemma tau_pi'' : forall A,
mIncluded_ind (tau A) (pi A).
Proof.
unfold pi, tau; unfold mIncluded_ind. intros A. induction (myEdges A).
- simpl. apply mInclNil.
- destruct a as [ev1 ev2]. simpl. 
destruct (myLabel A ev1), (myLabel A ev2).
-- auto.
-- eapply mInclLe.
---
Abort.

Lemma tau_pi : forall A,
 mIncluded (myEqDec_event A) (tau A) (pi A).
Proof.
 unfold pi, tau; unfold mIncluded; intros A. induction (myEdges A).
 - simpl. intros a HIn. inversion HIn.
 - destruct a as [ev1 ev2]. simpl. 
 destruct (myLabel A ev1), (myLabel A ev2).
 -- auto.
 -- intros a' HIn. destruct HIn; subst.
 --- simpl. destruct (myEqDec_event A a' a').
 ---- simpl. apply IHl. simpl in *. simpl. admit.
 -- simpl in *. admit.
Qed.

Lemma tau_pi : forall A ev,
 In ev (tau A) ->
 In ev (pi A).
Proof.
 unfold pi, tau; intros A ev H; 
 induction (myEdges A);
 try (inversion H; fail);
 destruct a as [ev1 ev2]; simpl in *;
 destruct (myLabel A ev1), (myLabel A ev2);
 try (repeat right; auto; fail); 
 destruct H; subst; simpl; auto.
Qed.

Lemma tau_pi : forall A,
 mIncluded_fix (myEqDec_labels A) (tau A) (pi A).
*)

End AdversarySets.