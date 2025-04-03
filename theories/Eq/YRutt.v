(** * Undefined-behaviour-sensitive relation up to tau *)

(** [X-rutt] is a generalization of [rutt] that supports the
representation of undefined behavior. It may also be regarded as a
generalization of rutt that can relate tree prefixes, i.e. trees up to
triggered events called cutoff points, beyond which the relation holds
trivially. The definition of [X-rutt] adds four extra clauses to that
of [rutt]. All the associated boilerplate comes from the refactoring
of Rutt.v. *)

(** Boolean predicates, given as additional parameters, are used to
partition events into cutoff events (if false) and regular,
interpretable ones (if true). Cutoff events can be used to represent
the semantics of undefined behaviour associated to source code
errors. *)

(* From the point of view of relational parametricity, it would be more fitting
  to replace [(REv, RAns)] with one [REv : forall A1 A2, (A1 -> A2 -> Prop) -> (E1 A1 -> E2 A2 -> Prop)].
  Contributions to that effect are welcome. *)

From Coq Require Import
     Morphisms
.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Utils
     Axioms
     ITree
     Eq
     Basics
.

From Paco Require Import paco.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(** Auxiliary notation *)

Notation DoCutoffF EE t := 
   (exists T (e: _ T) k, EE T e = false /\ t = VisF e k).

Notation DoCutoff EE t := (DoCutoffF EE (observe t)).

Notation WillCutoff EE t := 
    (exists T (e: _ T) k,
      EE T e = false /\ @eutt _ _ _ eq t (Vis e k)).

Notation IsCut EE e := (EE e = false).
Notation NoCut EE e := (EE e = true).
Notation IsCut_ EE A e := (EE A e = false).
Notation NoCut_ EE A e := (EE A e = true).

Section RuttF.

  Context {E1 E2 : Type -> Type}.
  Context {R1 R2 : Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).
  Context (ER1 : forall X, E1 X -> R2 -> Prop).
  Context (ER2 : forall X, E2 X -> R1 -> Prop).
  
  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop ).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop ).    
  Context (RR : R1 -> R2 -> Prop).
  
  Arguments EE1 {X}.
  Arguments EE2 {X}.
  Arguments ER1 {X}.
  Arguments ER2 {X}.
  Arguments REv {A} {B}.
  Arguments RAns {A} {B}.
  
  Inductive ruttF (sim : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2),
      RR r1 r2 ->
      ruttF sim (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1) (m2 : itree E2 R2),
      sim m1 m2 ->
      ruttF sim (TauF m1) (TauF m2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B )
                   (k1 : A -> itree E1 R1) (k2 : B -> itree E2 R2),
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> sim (k1 a) (k2 b)) ->
      ruttF sim (VisF e1 k1) (VisF e2 k2)
  | EqVisRet : forall (A : Type) (e1 : E1 A) (k1 : A -> itree E1 R1) (r2 : R2),
      IsCut EE1 e1 -> 
      ER1 e1 r2 ->
      ruttF sim (VisF e1 k1) (RetF r2)
  | EqRetVis : forall (A : Type) (e2 : E2 A) (k2 : A -> itree E2 R2) (r1 : R1),
      IsCut EE2 e2 -> 
      ER2 e2 r1 ->
      ruttF sim (RetF r1) (VisF e2 k2)
  | EqVisTau : forall (A : Type) (e1 : E1 A) (k1 : A -> itree E1 R1)
                      (m2 : itree E2 R2),
     IsCut EE1 e1 -> 
     sim (Vis e1 k1) m2 ->
     ruttF sim (VisF e1 k1) (TauF m2)
  | EqTauVis : forall (A : Type) (e2 : E2 A) (k2 : A -> itree E2 R2)
                      (m1 : itree E1 R1),
     IsCut EE2 e2 -> 
     sim m1 (Vis e2 k2) ->
     ruttF sim (TauF m1) (VisF e2 k2)
  | EqTauL : forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
      ruttF sim (observe t1) ot2 ->
      ruttF sim (TauF t1) ot2
  | EqTauR : forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
      ruttF sim ot1 (observe t2) ->
      ruttF sim ot1 (TauF t2).
  Hint Constructors ruttF : itree.

  Definition rutt_ (sim : itree E1 R1 -> itree E2 R2 -> Prop)
                   (t1 : itree E1 R1) (t2 : itree E2 R2) :=
    ruttF sim (observe t1) (observe t2).
  Hint Unfold rutt_ : itree.

  Lemma rutt_monot : monotone2 rutt_.
  Proof.
    red. intros. red; induction IN; eauto with itree.
  Qed.

  Definition rutt : itree E1 R1 -> itree E2 R2 -> Prop := paco2 rutt_ bot2.
  Hint Unfold rutt : itree.

  Lemma ruttF_inv_VisF_r {sim} t1 U2 (e2: E2 U2) (k2: U2 -> _) :
    ruttF sim t1 (VisF e2 k2) ->
    (exists U1 (e1: E1 U1) k1, t1 = VisF e1 k1 /\
         forall v1 v2, RAns e1 v1 e2 v2 -> sim (k1 v1) (k2 v2)) \/
    (exists (r1: R1), t1 = RetF r1 /\ IsCut EE2 e2 /\ ER2 e2 r1) \/
    (exists t1', t1 = TauF t1' /\ IsCut EE2 e2 /\ sim t1' (Vis e2 k2)) \/
    (exists t1', t1 = TauF t1' /\ ruttF sim (observe t1') (VisF e2 k2)).
  Proof.
    intros H; destruct t1. 
    - dependent destruction H; try congruence.
      right; left; eauto.
    - dependent destruction H; try congruence.
      + right; right; left; eauto.
      + repeat right; eauto.
    - dependent destruction H; try congruence.
      + left; eauto.
  Qed.
 
  Lemma ruttF_inv_VisF {sim}
      U1 U2 (e1 : E1 U1) (e2 : E2 U2) (k1 : U1 -> _) (k2 : U2 -> _)
    : ruttF sim (VisF e1 k1) (VisF e2 k2) ->
      forall v1 v2, RAns e1 v1 e2 v2 -> sim (k1 v1) (k2 v2).
  Proof.
    intros H. dependent destruction H. assumption.
  Qed.

  Ltac unfold_rutt :=
    (try match goal with [|- rutt_ _ _ _ _ _ _ _ _ _ _ _ ] => red end);
    (repeat match goal with [H: rutt_ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => red in H end).

  Lemma fold_ruttF:
    forall (t1: itree E1 R1) (t2: itree E2 R2) ot1 ot2,
    ruttF (upaco2 rutt_ bot2) ot1 ot2 ->
    ot1 = observe t1 ->
    ot2 = observe t2 ->
    rutt t1 t2.
  Proof.
    intros * eq -> ->; pfold; auto.
  Qed.

End RuttF.

Tactic Notation "fold_ruttF" hyp(H) :=
  try punfold H;
  try red in H;
  match type of H with
  | ruttF ?_EE1 ?_EE2 ?_ER1 ?_ER2 ?_REV ?_RANS ?_RR (upaco2 (rutt_ ?_EE1 ?_EE2 ?_ER1 ?_ER2 ?_REV ?_RANS ?_RR) bot2) ?_OT1 ?_OT2 =>
      match _OT1 with
      | observe _ => idtac
      | ?_OT1 => rewrite (itree_eta' _OT1) in H
      end;
      match _OT2 with
      | observe _ => idtac
      | ?_OT2 => rewrite (itree_eta' _OT2) in H
      end;
      eapply fold_ruttF in H; [| eauto | eauto]
  end.

#[global] Hint Resolve rutt_monot : paco.

Section ConstructionInversion.
  
  Variables (E1 E2: Type -> Type).
  Variables (R1 R2: Type).

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).
  Context (ER1 : forall X, E1 X -> R2 -> Prop).
  Context (ER2 : forall X, E2 X -> R1 -> Prop).

  Variable (REv: forall T1 T2, E1 T1 -> E2 T2 -> Prop).
  Variable (RAns: forall T1 T2, E1 T1 -> T1 -> E2 T2 -> T2 -> Prop).
  Variable (RR: R1 -> R2 -> Prop).

(*  Arguments EE1 {X}.
  Arguments EE2 {X}.
  Arguments ER1 {X}.
  Arguments ER2 {X}. *)
(*  Arguments REv {A} {B}.
  Arguments RAns {A} {B}. *)
 
Lemma rutt_Ret r1 r2:
  RR r1 r2 ->
  @rutt E1 E2 R1 R2 EE1 EE2 ER1 ER2 REv RAns RR
    (Ret r1: itree E1 R1) (Ret r2: itree E2 R2).
Proof. intros. pstep; constructor; auto. Qed.

Lemma rutt_inv_Ret r1 r2:
  rutt EE1 EE2 ER1 ER2 REv RAns RR (Ret r1) (Ret r2) -> RR r1 r2.
Proof.
  intros. punfold H. inv H. eauto.
Qed.

Lemma rutt_inv_Ret_l r1 t2:
  rutt EE1 EE2 ER1 ER2 REv RAns RR (Ret r1) t2 ->
   (exists r2, t2 ≳ Ret r2 /\ RR r1 r2) \/
   (exists U2 (e2 : E2 U2) (k2 : U2 -> itree E2 R2),
         t2 ≳ Vis e2 k2 /\ IsCut_ EE2 U2 e2 /\ ER2 U2 e2 r1).
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (RetF r1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate.
  - inversion Heqot1; subst. left; exists r2. split; [reflexivity|auto].
  - inversion Heqot1; subst. right; exists A, e2, k2. split; [reflexivity|auto].
  - destruct (IHHrutt Heqot1) as [ [r2 [H1 H2]] | [A [e2 [k2 [H1 H2]]]]].
    + left; exists r2; split; auto.
      rewrite <- itree_eta in H1. now rewrite tau_euttge.
    + right; exists A, e2, k2; split; auto.
      rewrite <- itree_eta in H1. now rewrite tau_euttge.
Qed.

Lemma rutt_inv_Ret_r t1 r2:
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 (Ret r2) ->
  (exists r1, t1 ≳ Ret r1 /\ RR r1 r2) \/
    (exists U1 (e1 : E1 U1) (k1 : U1 -> itree E1 R1),
        t1 ≳ Vis e1 k1/\ IsCut_ EE1 U1 e1 /\ ER1 U1 e1 r2).
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (RetF r2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate.
  - inversion Heqot2; subst. left; exists r1. split; [reflexivity|auto].
  - inversion Heqot2; subst. right; exists A, e1, k1. split; [reflexivity|auto].
  - destruct (IHHrutt Heqot2) as [ [r1 [H1 H2]] | [A [e1 [k1 [H1 H2]]]]].
    + left; exists r1; split; auto.
      rewrite <- itree_eta in H1. now rewrite tau_euttge.
    + right; exists A, e1, k1; split; auto.
      rewrite <- itree_eta in H1. now rewrite tau_euttge.
Qed.

Lemma rutt_inv_Tau_l t1 t2 :
  rutt EE1 EE2 ER1 ER2 REv RAns RR (Tau t1) t2 ->
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. genobs t2 ot2.
  hinduction H before t1; intros; try discriminate.
  - inv Heqtt1. pclearbot. pstep. red. simpobs.
    econstructor; eauto. pstep_reverse.
  - inv Heqtt1. rewrite Heqot2 in H0. 
    red in H0. pclearbot. punfold H0. pstep; auto.
  - inv Heqtt1. punfold_reverse H.
  - red in IHruttF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
Qed.

Lemma rutt_add_Tau_l t1 t2 :
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 t2 ->
  rutt EE1 EE2 ER1 ER2 REv RAns RR (Tau t1) t2.
Proof.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma rutt_inv_Tau_r t1 t2 :
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 (Tau t2) ->
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  pstep. red. remember (TauF t2) as tt2 eqn:Ett2 in H.
  revert t2 Ett2; induction H; try discriminate; intros; inversion Ett2; subst; auto.
  - pclearbot. constructor. pstep_reverse.
  - pclearbot. punfold H0.
  - constructor. eapply IHruttF; eauto.
Qed.

Lemma rutt_add_Tau_r t1 t2 :
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 t2 ->
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 (Tau t2).
Proof.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma rutt_inv_Tau t1 t2 :
  rutt EE1 EE2 ER1 ER2 REv RAns RR (Tau t1) (Tau t2) ->
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 t2.
Proof.
  intros; apply rutt_inv_Tau_r, rutt_inv_Tau_l; assumption.
Qed.

Lemma rutt_Vis {T1 T2} (e1: E1 T1) (e2: E2 T2)
    (k1: T1 -> itree E1 R1) (k2: T2 -> itree E2 R2):
  REv _ _ e1 e2 ->
  (forall t1 t2, RAns _ _ e1 t1 e2 t2 ->
                 rutt EE1 EE2 ER1 ER2 REv RAns RR (k1 t1) (k2 t2)) ->
                 rutt EE1 EE2 ER1 ER2 REv RAns RR (Vis e1 k1) (Vis e2 k2).
Proof.
  intros He Hk. pstep; constructor; auto.
  intros; left. apply Hk; auto.
Qed.

Lemma rutt_inv_Vis_l {U1} (e1: E1 U1) k1 t2:
  rutt EE1 EE2 ER1 ER2 REv RAns RR (Vis e1 k1) t2 ->
  (exists U2 (e2: E2 U2) k2,
    t2 ≈ Vis e2 k2 /\
    REv _ _ e1 e2 /\
    (forall v1 v2, RAns _ _ e1 v1 e2 v2 ->
                     rutt EE1 EE2 ER1 ER2 REv RAns RR (k1 v1) (k2 v2))) \/
    (exists (r2: R2), t2 ≈ Ret r2 /\ IsCut_ EE1 U1 e1 /\ ER1 U1 e1 r2) \/
    (exists t2', t2 ≳ Tau t2' /\ IsCut_ EE1 U1 e1 /\
                   rutt EE1 EE2 ER1 ER2 REv RAns RR (Vis e1 k1) t2').
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (VisF e1 k1) as ot1; revert Heqot1. 
  induction Hrutt; intros; try discriminate; subst.  
  - inversion Heqot1; subst A. inversion_sigma. rewrite <- eq_rect_eq in *;
    subst; rename B into U2; left.
    exists U2, e2, k2; split.
    reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H0 v1 v2 HAns). red in H0. now pclearbot.
  - dependent destruction Heqot1.
    right; left. exists r2; split; eauto; reflexivity.  
  - dependent destruction Heqot1.
    right; right.
    exists m2. split; auto. reflexivity. split; auto. pclearbot. auto.
  - destruct (IHHrutt eq_refl) as [(U2 & e2 & k2 & Ht0 & HAns) |
                                    [[r2 [H0 [H1 H2]]] | [r2 [H0 [H1 H2]]]]].
    + rewrite <- itree_eta in Ht0.
      left. exists U2, e2, k2; split; auto. now rewrite tau_eutt.
    + right; right. exists t0; split; auto. reflexivity.
      split; auto. pstep; red. auto.
    + specialize (IHHrutt eq_refl).
      destruct IHHrutt.
      * setoid_rewrite <- (itree_eta t0) in H.
        left.
        destruct H as [U2 [e2 [k2 [K [K0 K1]]]]].
        exists U2, e2, k2; split; auto.
        eapply eqit_Tau_l.
        auto.
      * destruct H.
        -- setoid_rewrite <- (itree_eta t0) in H.
           right. left.
           destruct H as [r3 [K1 [K2 K3]]].
           exists r3; split; auto.
           eapply eqit_Tau_l; auto.
        -- setoid_rewrite <- (itree_eta t0) in H.
           right; right.
           destruct H as [t3 [K [K0 K1]]].
           exists t3; split; auto.
           eapply eqit_Tau_l; auto.
Qed.           

Lemma rutt_inv_Vis_r {U2} t1 (e2: E2 U2) k2:
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 (Vis e2 k2) ->
  (exists U1 (e1: E1 U1) k1,
    t1 ≈ Vis e1 k1 /\
    REv U1 U2 e1 e2 /\
    (forall v1 v2, RAns _ _ e1 v1 e2 v2 ->
                     rutt EE1 EE2 ER1 ER2 REv RAns RR (k1 v1) (k2 v2))) \/
    (exists (r1: R1), t1 ≈ Ret r1 /\ IsCut_ EE2 U2 e2 /\ ER2 U2 e2 r1) \/
    (exists t1', t1 ≳ Tau t1' /\ IsCut_ EE2 U2 e2 /\
                   rutt EE1 EE2 ER1 ER2 REv RAns RR t1' (Vis e2 k2)).      
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (VisF e2 k2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot2; subst B. inversion_sigma. rewrite <- eq_rect_eq in *;
    subst; rename A into U1; left.
    exists U1, e1, k1; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H0 v1 v2 HAns). red in H0. now pclearbot.
  - dependent destruction Heqot2.
    right; left. exists r1; split; eauto; reflexivity.  
  - dependent destruction Heqot2.
    right; right.
    exists m1. split; auto. reflexivity. split; auto. pclearbot. auto.

  - destruct (IHHrutt eq_refl) as [(U1 & e1 & k1 & Ht0 & HAns) |
                                    [[r1 [H0 [H1 H2]]] | [r1 [H0 [H1 H2]]]]].
    + rewrite <- itree_eta in Ht0.
      left. exists U1, e1, k1; split; auto. now rewrite tau_eutt.
    + right; right. exists t0; split; auto. reflexivity.
      split; auto. pstep; red. auto.
    + specialize (IHHrutt eq_refl).
      destruct IHHrutt.
      * setoid_rewrite <- (itree_eta t0) in H.
        left.
        destruct H as [U1 [e1 [k1 [K [K0 K1]]]]].
        exists U1, e1, k1; split; auto.
        eapply eqit_Tau_l.
        auto.
      * destruct H.
        -- setoid_rewrite <- (itree_eta t0) in H.
           right. left.
           destruct H as [r3 [K1 [K2 K3]]].
           exists r3; split; auto.
           eapply eqit_Tau_l; auto.
        -- setoid_rewrite <- (itree_eta t0) in H.
           right; right.
           destruct H as [t3 [K [K0 K1]]].
           exists t3; split; auto.
           eapply eqit_Tau_l; auto.
Qed.           

Lemma rutt_inv_Vis U1 U2 (e1: E1 U1) (e2: E2 U2)
    (k1: U1 -> itree E1 R1) (k2: U2 -> itree E2 R2):
  rutt EE1 EE2 ER1 ER2 REv RAns RR (Vis e1 k1) (Vis e2 k2) ->
  forall u1 u2, RAns U1 U2 e1 u1 e2 u2 ->
                rutt EE1 EE2 ER1 ER2 REv RAns RR (k1 u1) (k2 u2).
Proof.
  intros H u1 u2 Hans. punfold H.
  apply ruttF_inv_VisF with (v1 := u1) (v2 := u2) in H. pclearbot; auto.
  assumption.
Qed.
End ConstructionInversion.

Section euttge_trans_clo.

  Context {E1 E2 : Type -> Type} {R1 R2 : Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).
  Context (ER1 : forall X, E1 X -> R2 -> Prop).
  Context (ER2 : forall X, E2 X -> R1 -> Prop).
  
  Context (RR : R1 -> R2 -> Prop).

  (* Closing a relation over itrees under [euttge].
     Essentially the same closure as [eqit_trans_clo], but heterogeneous
     in the interface argument [E].
     We only define the closure under [euttge] as opposed to [eqit_trans_clo]
     capturing closure under [eq_itree] and [eutt] at the same time, since it's
     the only one we need.
   *)

  (* A transitivity functor *)
  Variant euttge_trans_clo (rr : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree E1 R1 -> itree E2 R2 -> Prop :=
    | eqit_trans_clo_intro t1 t2 t1' t2'
        (RR1: R1 -> R1 -> Prop)
        (RR2: R2 -> R2 -> Prop)
        (EQVl: euttge RR1 t1 t1')
        (EQVr: euttge RR2 t2 t2')
        (REL: rr t1' t2')
        (LEER1: forall A1 (e1: E1 A1) y y', IsCut_ EE1 _ e1 ->
                  RR2 y y' -> ER1 _ e1 y' -> ER1 _ e1 y)
        (LEER2: forall A2 (e2: E2 A2) x x', IsCut_ EE2 _ e2 ->
                  RR1 x x' -> ER2 _ e2 x' -> ER2 _ e2 x) 
        (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
        (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y) :
      euttge_trans_clo rr t1 t2.

  (*
    | eqit_trans_clo_lcut_intro {A1} (e1: E1 T) k
        (t1: itree E1 R1) (t2: itree E2 R2) t2'
        (CT: IsCut EE1 A1 e1)
        (EU: euttge RR2 t2 t2')
        (OE1: observe t1 = VisF e k) (OE2: observe t2 = TauF t2') 
        (REL: rr t1 t2') :
      euttge_trans_clo rr t1 t2

                       
    |  eqit_trans_clo_intro_ER1 A1 (e1: E1 A1) y y'
      (RR2: R2 -> R2 -> Prop)
      (IC1: IsCut EE1 _ e1)
      (RR2_hyp: RR2 y y'),
        ER1 _ e1 y' -> ER1 _ e1 y)
         
      
    | eqit_trans_clo_lcut_intro {T} (e: E1 T) k
        (t1: itree E1 R1) (t2: itree E2 R2) t2'
        (CT: IsCut EE1 T e)
        (OE1: observe t1 = VisF e k) (OE2: observe t2 = TauF t2') 
        (REL: rr t1 t2') :
      euttge_trans_clo rr t1 t2
    | eqit_trans_clo_rcut_intro {T} (e: E2 T) k
        (t1: itree E1 R1) (t2: itree E2 R2) t1'
        (CT: IsCut EE2 T e)
        (OE1: observe t1 = TauF t1') (OE2: observe t2 = VisF e k)
        (REL: rr t1' t2) :
      euttge_trans_clo rr t1 t2.
*)

(*  
  (* A transitivity functor *)
  Variant euttge_trans_clo (rr : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree E1 R1 -> itree E2 R2 -> Prop :=
    | eqit_trans_clo_intro t1 t2 t1' t2'
        (RR1: R1 -> R1 -> Prop)
        (RR2: R2 -> R2 -> Prop)
        (EQVl: euttge RR1 t1 t1')
        (EQVr: euttge RR2 t2 t2')
        (REL: rr t1' t2')
        (LEER1: forall A1 (e1: E1 A1) y y',
                  RR2 y y' -> ER1 _ e1 y' -> ER1 _ e1 y)
        (LEER2: forall A2 (e2: E2 A2) x x',
                  RR1 x x' -> ER2 _ e2 x' -> ER2 _ e2 x)
        (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
        (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y) :
      euttge_trans_clo rr t1 t2
    | eqit_trans_clo_lcut_intro {T} (e: E1 T) k
        (t1: itree E1 R1) (t2: itree E2 R2) t2'
        (CT: IsCut EE1 T e)
        (OE1: observe t1 = VisF e k) (OE2: observe t2 = TauF t2') 
        (REL: rr t1 t2') :
      euttge_trans_clo rr t1 t2
    | eqit_trans_clo_rcut_intro {T} (e: E2 T) k
        (t1: itree E1 R1) (t2: itree E2 R2) t1'
        (CT: IsCut EE2 T e)
        (OE1: observe t1 = TauF t1') (OE2: observe t2 = VisF e k)
        (REL: rr t1' t2) :
      euttge_trans_clo rr t1 t2.
*)
  
  Hint Constructors euttge_trans_clo : itree.

  Lemma euttge_trans_clo_mon r1 r2 t1 t2
        (IN : euttge_trans_clo r1 t1 t2)
        (LE : r1 <2= r2) :
    euttge_trans_clo r2 t1 t2.
  Proof.
    destruct IN.
    econstructor 1; eauto.
  Qed.    
(*    econstructor 2; eauto.
    econstructor 3; eauto.
  Qed.
*)

  Hint Resolve euttge_trans_clo_mon : paco.

End euttge_trans_clo.

(* From ITree Require Import EqAxiom. *)

(*replicate this proof for the models functor*)
(* Validity of the up-to [euttge] principle *)
Lemma euttge_trans_clo_wcompat E1 E2 R1 R2
  (EE1: forall {X}, E1 X -> bool)
  (EE2: forall {X}, E2 X -> bool)
  (ER1 : forall {X}, E1 X -> R2 -> Prop)
  (ER2 : forall {X}, E2 X -> R1 -> Prop)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  (RR : R1 -> R2 -> Prop) :
  wcompatible2 (rutt_ (@EE1) (@EE2) (@ER1) (@ER2) REv RAns RR)
    (euttge_trans_clo (@EE1) (@EE2) (@ER1) (@ER2) RR).
Proof.
  constructor; eauto with paco.
  { red. intros. eapply euttge_trans_clo_mon; eauto. }
  intros.
  destruct PR.  punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto; (try constructor; eauto).
    remember (RetF r3) as x. hinduction EQVr before r; intros; subst; try inv Heqx; (try constructor; eauto).
  - red. remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; ( try (constructor; eauto; fail )).
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. constructor. gclo. econstructor; eauto with paco.
  - remember (VisF e1 k1) as x. red.
    hinduction EQVl before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqx.
    dependent destruction Heqy.
    constructor; auto. intros. apply H0 in H1. pclearbot.    
    apply gpaco2_clo.
    econstructor; eauto with itree.
  - remember (VisF e1 k1) as x. red.
    hinduction EQVl before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    remember (RetF r2) as y.
    hinduction EQVr before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqx.
    dependent destruction Heqy.
    constructor; auto. eapply (LEER1 A e1); eauto.
  - remember (RetF r1) as x. red.
    hinduction EQVl before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    remember (VisF e2 k2) as y.
    hinduction EQVr before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqx.
    dependent destruction Heqy.
    constructor; auto. eapply (LEER2 A e2); eauto.
  - remember (VisF e1 k1) as x. red.
(*    remember (TauF m2) as y. red. *)
    hinduction EQVl before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqx.
    remember (TauF m2) as y.
    hinduction EQVr before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqy.
    econstructor; eauto. pclearbot.
    eapply gpaco2_clo; eauto.
    econstructor; eauto.
    eapply eqit_Vis; eauto.
  - remember (VisF e2 k2) as y. red.
    hinduction EQVr before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqy.
    remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    dependent destruction Heqx.
    econstructor; eauto. pclearbot.
    eapply gpaco2_clo; eauto.
    econstructor; eauto.
    eapply eqit_Vis; eauto.    
  - remember (TauF t1) as x. red.
    hinduction EQVl before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    pclearbot. punfold REL.
    dependent destruction Heqx.
    constructor; auto. eapply IHREL; eauto.
  - remember (TauF t2) as y. red.
    hinduction EQVr before r; intros; subst; try discriminate; try (constructor; eauto; fail).
    pclearbot. punfold REL.
    dependent destruction Heqy.
    constructor; auto. eapply IHREL; eauto.
Qed.

#[global] Hint Resolve euttge_trans_clo_wcompat : paco.

(* The validity of the up-to [euttge] entails we can rewrite under [euttge]
   and hence also [eq_itree] during coinductive proofs of [rutt]
*)
#[global] Instance grutt_cong_eqit {R1 R2 : Type} {E1 E2 : Type -> Type}
       (EE1: forall {X}, E1 X -> bool)
       (EE2: forall {X}, E2 X -> bool)
       (ER1 : forall {X}, E1 X -> R2 -> Prop)
       (ER2 : forall {X}, E2 X -> R1 -> Prop)
       {REv : forall A B, E1 A -> E2 B -> Prop}
       {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RR1 RR2}
       {RS : R1 -> R2 -> Prop} r rg
       (LEER1: forall A (e1:E1 A) y y',
           (RR2 y y':Prop) -> ER1 e1 y' -> ER1 e1 y)
       (LEER2: forall A (e2:E2 A) x x',
           (RR1 x x':Prop) -> ER2 e2 x' -> ER2 e2 x)
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
    (gpaco2 (rutt_ (@EE1) (@EE2) (@ER1) (@ER2) REv RAns RS)
             (euttge_trans_clo (@EE1) (@EE2) (@ER1) (@ER2) RS) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto;
    try eapply eqit_mon; try apply H; try apply H0; auto.
Qed.

Global Instance grutt_cong_euttge {R1 R2 : Type} {E1 E2 : Type -> Type}
       (EE1: forall {X}, E1 X -> bool)
       (EE2: forall {X}, E2 X -> bool)
       (ER1 : forall {X}, E1 X -> R2 -> Prop)
       (ER2 : forall {X}, E2 X -> R1 -> Prop)
       {REv : forall A B, E1 A -> E2 B -> Prop}
       {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} {RR1 RR2}
       {RS : R1 -> R2 -> Prop} r rg
       (LEER1: forall A (e1:E1 A) y y',
           (RR2 y y':Prop) -> ER1 e1 y' -> ER1 e1 y)
       (LEER2: forall A (e2:E2 A) x x',
           (RR1 x x':Prop) -> ER2 e2 x' -> ER2 e2 x)
       (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
       (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
  Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
    (gpaco2 (rutt_ (@EE1) (@EE2) (@ER1) (@ER2) REv RAns RS)
       (euttge_trans_clo (@EE1) (@EE2) (@ER1) (@ER2) RS) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto.
Qed.

(* Provide these explicitly since typeclasses eauto cannot infer them *)

#[global] Instance grutt_cong_eqit_eq {R1 R2 : Type} {E1 E2 : Type -> Type}
       (EE1: forall {X}, E1 X -> bool)
       (EE2: forall {X}, E2 X -> bool)
       (ER1 : forall {X}, E1 X -> R2 -> Prop)
       (ER2 : forall {X}, E2 X -> R1 -> Prop)
       {REv : forall A B, E1 A -> E2 B -> Prop}
       {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} 
       {RS : R1 -> R2 -> Prop} r rg :
    Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
      (gpaco2 (rutt_ (@EE1) (@EE2) (@ER1) (@ER2) REv RAns RS)
         (euttge_trans_clo (@EE1) (@EE2) (@ER1) (@ER2) RS) r rg).
Proof.
  apply grutt_cong_eqit; now intros * ->.
Qed.

#[global] Instance grutt_cong_euttge_eq {R1 R2 : Type} {E1 E2 : Type -> Type}
       (EE1: forall {X}, E1 X -> bool)
       (EE2: forall {X}, E2 X -> bool)
       (ER1 : forall {X}, E1 X -> R2 -> Prop)
       (ER2 : forall {X}, E2 X -> R1 -> Prop)
       {REv : forall A B, E1 A -> E2 B -> Prop}
       {RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop} 
       {RS : R1 -> R2 -> Prop} r rg :
    Proper (euttge eq ==> euttge eq ==> flip impl)
      (gpaco2 (rutt_ (@EE1) (@EE2) (@ER1) (@ER2) REv RAns RS)
         (euttge_trans_clo (@EE1) (@EE2) (@ER1) (@ER2) RS) r rg).
Proof.
  apply grutt_cong_euttge; now intros * ->.
Qed.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Lemma rutt_weaken (E1 E2: Type -> Type) (R1 R2 : Type)
       (EE1 EE1': forall {X}, E1 X -> bool)
       (EE2 EE2': forall {X}, E2 X -> bool)
       (ER1 ER1': forall {X}, E1 X -> R2 -> Prop)
       (ER2 ER2': forall {X}, E2 X -> R1 -> Prop)
       {REv REv': forall A B, E1 A -> E2 B -> Prop}
       {RAns RAns': forall A B, E1 A -> A -> E2 B -> B -> Prop} 
       {RR RR': R1 -> R2 -> Prop} (t1: itree E1 R1) (t2: itree E2 R2) :

  (forall A (e1: E1 A) (r2:R2), ER1 e1 r2 -> ER1' e1 r2) ->
  (forall A (e2: E2 A) (r1:R1), ER2 e2 r1 -> ER2' e2 r1) -> 

  (forall A (e1: E1 A), (EE1 e1 = false) -> (EE1' e1 = false)) ->
  (forall A (e2: E2 A), (EE2 e2 = false) -> (EE2' e2 = false)) ->
  
  (forall T1 T2 (e1 : E1 T1) (e2 : E2 T2),
    REv T1 T2 e1 e2 -> REv' T1 T2 e1 e2) ->

  (forall T1 T2 (e1 : E1 T1) (t1 : T1) (e2 : E2 T2) (t2 : T2) ,
    RAns' T1 T2 e1 t1 e2 t2 -> RAns T1 T2 e1 t1 e2 t2) ->

  (forall r1 r2, RR r1 r2 -> RR' r1 r2) ->

  rutt (@EE1) (@EE2) (@ER1) (@ER2) REv RAns RR t1 t2 ->
  rutt (@EE1') (@EE2') (@ER1') (@ER2') REv' RAns' RR' t1 t2.
Proof.
  move => hEE1 hEE2 HER1 hER2 hREv hRAns hRR. move: t1 t2.
  pcofix CIH.
 (* have CIH0 : forall (a0 : itree E1 R1) (a1 : itree E2 R2), bot2 a0 a1 -> r a0 a1 by done. *)
  move => t1 t2 h.
  pstep. punfold h. red in h |- *.
(*  have up_bot_r: (forall m1 m2,
    upaco2 (rutt_ (@EE1) (@EE2) (@ER1) (@ER2) REv RAns RR) bot2 m1 m2 ->
    upaco2 (rutt_ (@EE1') (@EE2') (@ER1') (@ER2') REv' RAns' RR') r m1 m2). 
  + pclearbot. move=> m1 m2 hm. right. eapply CIH; eauto. 
    case: hm; [ apply CIH | apply CIH0].  *)
  hinduction h before CIH; intros; subst.
  + by apply EqRet; auto.
  + econstructor; eauto with paco itree. right. eapply CIH; eauto. red in H.
    pclearbot; auto.
  + eapply EqVis; eauto; intros.
    right. eapply CIH; eauto.
    eapply hRAns in H1; eauto.
    specialize (H0 a b H1).
    pclearbot; auto.
  + eapply EqVisRet; eauto. 
  + eapply EqRetVis; eauto.  
  + eapply EqVisTau; eauto.
    right. eapply CIH; eauto.
    pclearbot; auto.
  + eapply EqTauVis; eauto.
    right. eapply CIH; eauto.
    pclearbot; auto.
  + eapply EqTauL; eauto.  
  + eapply EqTauR; eauto.  
Qed.

#[local] Notation prerel E D := (forall A B : Type, E A -> D B -> Prop).
#[local] Notation postrel E D := (forall A B : Type, E A -> A -> D B -> B -> Prop).

Variant prcompose {E1 E2 E3 : Type -> Type}
  (pre : prerel E1 E2) (pre' : prerel E2 E3) T1 T3 (e1 : E1 T1) (e3 : E3 T3) : Prop :=
| Cprerel T2 (e2 :E2 T2) (REL1 : pre T1 T2 e1 e2) (REL2 : pre' T2 T3 e2 e3).

(*
Variant pocompose {E1 E2 E3 : Type -> Type}
  (post : postrel E1 E2) (post' : postrel E2 E3)
  T1 T3 (e1 : E1 T1) (t1 : T1) (e3 : E3 T3) (t3 : T3) : Prop :=
| Cpostrel T2 (e2:E2 T2) (t2:T2) (REL1: post T1 T2 e1 t1 e2 t2) (REL2 : post' T2 T3 e2 t2 e3 t3).
*)

Definition pocompose {E1 E2 E3 : Type -> Type}
  (pre : prerel E1 E2) (pre' : prerel E2 E3)
  (post : postrel E1 E2) (post' : postrel E2 E3)
  T1 T3 (e1 : E1 T1) (t1 : T1) (e3 : E3 T3) (t3 : T3) : Prop :=
  forall T2 (e2: E2 T2),
    pre T1 T2 e1 e2 -> pre' T2 T3 e2 e3 ->
    exists2 t2, post T1 T2 e1 t1 e2 t2 & post' T2 T3 e2 t2 e3 t3.

Variant rrcompose  {E2 : Type -> Type} {R1 R2 R3 : Type}
  (ER21 : forall A, E2 A -> R1 -> Prop)
  (ER23 : forall A, E2 A -> R3 -> Prop)
  (RR12  : R1 -> R2 -> Prop)
  (RR23  : R2 -> R3 -> Prop)
  (r1 : R1) (r3 : R3) : Prop :=
| RRcompose_RR_RR (r2 : R2) (h : RR12 r1 r2) (h' : RR23 r2 r3)
| RRcompose_RE_ER A2 (e2 : E2 A2) (h : ER21 A2 e2 r1) (h' : ER23 A2 e2 r3).

Variant ercompose {E1 E2 : Type -> Type} {R2 R3 : Type}
  (EE1: forall {X}, E1 X -> bool)                
  (EE2: forall {X}, E2 X -> bool)                
  (REv12 :  prerel E1 E2)
  (RR23  : R2 -> R3 -> Prop)
  (ER12  : forall A, E1 A -> R2 -> Prop)
  (ER23  : forall A, E2 A -> R3 -> Prop) A1
  (e1 : E1 A1) (r3 : R3) : Prop :=
| ERcompose_ER_RR (r2 : R2) (h : ER12 A1 e1 r2) (h' : RR23 r2 r3)
| ERcompose_EE_ER A2 (e2 : E2 A2) (h : REv12 A1 A2 e1 e2) (h' : ER23 A2 e2 r3).

Variant recompose {E2 E3 : Type -> Type} {R1 R2 : Type}
  (EE2: forall {X}, E2 X -> bool)                
  (EE3: forall {X}, E3 X -> bool)                
  (REv23 : prerel E2 E3)
  (RR12  : R1 -> R2 -> Prop)
  (RE12  : forall A, E2 A -> R1 -> Prop)
  (RE23  : forall A, E3 A -> R2 -> Prop) A3
  (e3 : E3 A3) (r1 : R1) : Prop :=
| REcompose_RR_RE (r2 : R2) (h : RR12 r1 r2) (h' : RE23 A3 e3 r2)
| REcompose_RE_EE A2 (e2 : E2 A2) (h : RE12 A2 e2 r1) (h' : REv23 A2 A3 e2 e3).

Fail Lemma rutt_trans {E1 E2 E3: Type -> Type} {R1 R2 R3 : Type}
  (EE1: forall {X}, E1 X -> bool)
  (EE2 EE2': forall {X}, E2 X -> bool)
  (EE3: forall {X}, E3 X -> bool)
  (ER12 : forall {X}, E1 X -> R2 -> Prop)
  (ER23 : forall {X}, E2 X -> R3 -> Prop)
  (ER32 : forall {X}, E3 X -> R2 -> Prop)
  (ER21 : forall {X}, E2 X -> R1 -> Prop)
  (REv12 : prerel E1 E2)
  (REv23 : prerel E2 E3)
  (RAns12: postrel E1 E2)
  (RAns23: postrel E2 E3)
  (RR12 : R1 -> R2 -> Prop)
  (RR23 : R2 -> R3 -> Prop) 
  t1 t2 t3 :
  (forall A (e2: E2 A), (EE2 e2 = false) -> (EE2' e2 = false)) ->
  forall (INL : rutt (@EE1) (@EE2) (@ER12) (@ER21) REv12 RAns12 RR12 t1 t2) 
         (INR : rutt (@EE2) (@EE3) (@ER23) (@ER32) REv23 RAns23 RR23 t2 t3),
    rutt (@EE1) (@EE3)
      (ercompose (@EE1) (@EE2) (@REv12) RR23 (@ER12) (@ER23))
      (recompose (@EE2') (@EE3) (@REv23) RR12 (@ER21) (@ER32))
      (prcompose REv12 REv23)
      (pocompose RAns12 RAns23)
      (rrcompose (@ER21) (@ER23) RR12 RR23) t1 t3. 
(*
Proof.
  intros H. revert t1 t2 t3.
  pcofix CIH.
  intros t1 t2 t3 H0 H1.
  punfold H0.
  punfold H1.
  red in H0. red in H1.
  (* remember t1 as it1.
  remember t2 as it2.
  remember t3 as it3. *)
 (* revert H1. revert t3. *)
  dependent induction H0.
  { (* intros t3 H1. *)
    dependent induction H1; try congruence.
    { intros. pstep. red. simpl.
      rewrite <- x0.
      rewrite <- x.
      econstructor; eauto.
      econstructor; eauto.
      rewrite <- x1 in x2.
      inv x2. auto.
    }
    { intros. pstep. red. simpl.
      rewrite <- x0.
      rewrite <- x.
      econstructor; eauto.
      econstructor; eauto.
      rewrite <- x1 in x2.
      inv x2. auto.
    }  
    { intros.
      pstep. red. simpl.
      rewrite <- x0.
      rewrite <- x.
      econstructor; eauto.

      assert (paco2
    (rutt_ EE1 EE3 (ercompose EE1 EE2 REv12 RR23 ER12 ER23)
       (recompose EE2' EE3 REv23 RR12 ER21 ER32) (prcompose REv12 REv23)
       (pocompose RAns12 RAns23) (rrcompose ER21 ER23 RR12 RR23))
    r t1 t0) as A1.
      { eapply IHruttF; eauto. }

      punfold A1. red in A1. rewrite x0; auto.
    }
  }
  
  { dependent induction H1; try congruence.
    { pstep; red; simpl.
      rewrite <- x0.
      rewrite <- x.
      rewrite <- x1 in x2.
      inv x2. pclearbot.
      econstructor; eauto.
    }
    { pstep; red; simpl.
      rewrite <- x0.
      rewrite <- x.
      rewrite <- x1 in x2.
      inv x2. pclearbot.
      eapply EqTauVis; eauto.
    }
    { pstep; red; simpl.
      rewrite <- x0.
      rewrite <- x1 in x.
      inv x. pclearbot.
      eapply EqTauL. simpl.

      assert (paco2
      (rutt_ EE1 EE3 (ercompose EE1 EE2 REv12 RR23 ER12 ER23) (recompose EE2' EE3 REv23 RR12 ER21 ER32)
         (prcompose REv12 REv23) (pocompose RAns12 RAns23) (rrcompose ER21 ER23 RR12 RR23))
      r m1 t3) as A. 
      
      eapply IHruttF; eauto.
      admit. admit.
      punfold A.
Abort.
*)

Fail Lemma rutt_trans {E1 E2 E3: Type -> Type} {R1 R2 R3 : Type}
  (EE1: forall {X}, E1 X -> bool)
  (EE2 EE2': forall {X}, E2 X -> bool)
  (EE3: forall {X}, E3 X -> bool)
  (ER12 : forall {X}, E1 X -> R2 -> Prop)
  (ER23 : forall {X}, E2 X -> R3 -> Prop)
  (ER32 : forall {X}, E3 X -> R2 -> Prop)
  (ER21 : forall {X}, E2 X -> R1 -> Prop)
  (REv12 : prerel E1 E2)
  (REv23 : prerel E2 E3)
  (RAns12: postrel E1 E2)
  (RAns23: postrel E2 E3)
  (RR12 : R1 -> R2 -> Prop)
  (RR23 : R2 -> R3 -> Prop) 
  t1 t2 t3 :
  (forall A (e2: E2 A), (EE2 e2 = false) -> (EE2' e2 = false)) ->
  forall (INL : rutt (@EE1) (@EE2) (@ER12) (@ER21) REv12 RAns12 RR12 t1 t2) 
         (INR : rutt (@EE2) (@EE3) (@ER23) (@ER32) REv23 RAns23 RR23 t2 t3),
    rutt (@EE1) (@EE3)
      (ercompose (@EE1) (@EE2) (@REv12) RR23 (@ER12) (@ER23))
      (recompose (@EE2') (@EE3) (@REv23) RR12 (@ER21) (@ER32))
      (prcompose REv12 REv23)
      (pocompose RAns12 RAns23)
      (rrcompose (@ER21) (@ER23) RR12 RR23) t1 t3. 

(*  
  intros H. revert t1 t2 t3.
  pcofix CIH.
  intros t1 t2 t3 H0 H1.
  punfold H0.
  punfold H1.
  red in H0. red in H1.
 (* remember t1 as it1.
  remember t2 as it2.
  remember t3 as it3. *)
 (* revert H1. revert t3. *)
  dependent induction H0.
  { (* Ret1 Ret2 t3 *)
    dependent induction H1; try congruence.
    { intros. pstep. red. simpl.
      rewrite <- x0.
      rewrite <- x.
      econstructor; eauto.
      econstructor; eauto.
      rewrite <- x1 in x2.
      inv x2. auto.
    }
    { intros. pstep. red. simpl.
      rewrite <- x0.
      rewrite <- x.
      econstructor; eauto.
      econstructor; eauto.
      rewrite <- x1 in x2.
      inv x2. auto.
    }  
    { intros.
      pstep. red. simpl.
      rewrite <- x0.
      rewrite <- x.
      econstructor; eauto.

      assert (paco2
    (rutt_ EE1 EE3 (ercompose EE1 EE2 REv12 RR23 ER12 ER23)
       (recompose EE2' EE3 REv23 RR12 ER21 ER32) (prcompose REv12 REv23)
       (pocompose RAns12 RAns23) (rrcompose ER21 ER23 RR12 RR23))
    r t1 t0) as A1.
      { eapply IHruttF; eauto. }

      punfold A1. red in A1. rewrite x0; auto.
    }
  }
  
  { (* Tau1 Tau2 t3 *)
    pstep; red; simpl.
    rewrite <- x0.
    clear x0.

    (***)
    rewrite <- x in H1.
    pclearbot.

    (*
    assert (paco2 (rutt_ EE1 EE2 ER12 ER21 REv12 RAns12 RR12) bot2
              (Tau m1) m2) as H2.
    { punfold H0.
      pstep. red.
      eapply EqTauL; eauto. }

    clear H0.
     *)

    (* eapply EqTauL. *)

    clear x.

    dependent destruction H1.
    red in H1.
    destruct H1; eauto.
    
    dependent induction H1; try congruence.
    { pclearbot. 
      rewrite <- x.
      econstructor; eauto.
    }
    { pclearbot.
      rewrite <- x.
      eapply EqTauVis; eauto.
    }
    { pclearbot.
      (*   eapply EqTauL. simpl. *)
      specialize (IHruttF EE1 ER12 ER21 REv12 RAns12 RR12 m1).

      eapply IHruttF; eauto.
      rewrite x; auto.
      
      assert (paco2
                (rutt_ EE1 EE3 (ercompose EE1 EE2 REv12 RR23 ER12 ER23)
                   (recompose EE2' EE3 REv23 RR12 ER21 ER32)
                   (prcompose REv12 REv23)
                   (pocompose RAns12 RAns23)
                   (rrcompose ER21 ER23 RR12 RR23))
                   r (Tau m1) t3) as A. 

      eapply IHruttF; eauto.
      admit. admit.
      punfold A.
Abort.
*)


