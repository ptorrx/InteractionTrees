(** * Relation up to tau *)

(** [rutt] ("relation up to tau") is a generalization of [eutt] that may relate trees
  indexed by different event type families [E]. *)

(** It corresponds roughly to the interpretation of "types as relations" from the relational
  parametricity model by Reynolds (Types, Abstraction and Parametric Polymorphism).
  Any polymorphic function [f : forall E R, itree E R -> ...] should respect this relation,
  in the sense that for any relations [rE], [rR], the implication
  [rutt rE rR t t' -> (f t ~~ f t')] should hold, where [~~] is some canonical relation on the
  codomain of [f].

  If we could actually quotient itrees "up to taus", and Coq could generate
  parametricity ("free") theorems on demand, the above might be a free theorem. *)

(** [rutt] is used to define the [trace_refine] relation in [ITree.ITrace.ITraceDefinition]. *)

From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Utils
     Axioms
     ITree
     Eq
     Basics.

From Paco Require Import paco.

Require Import List.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

(** Auxiliary ********************************************************)

Class FIso (E1 E2: Type -> Type) := {
    mfun1: E1 -< E2 ;
    mfun2: E2 -< E1 ; 
    mid12 : forall T x, mfun1 T (mfun2 T x) = x ; 
    mid21 : forall T x, mfun2 T (mfun1 T x) = x ;
}.

Section ProjAux.
  Context {E: Type -> Type}.
  Context {E1: Type -> Type}.
  Context {E2: Type -> Type}.
  Context (EE : FIso E (E1 +' E2)).
 
  Definition LSub : E1 -< E := 
    match EE with
     {| mfun1 := f1; mfun2 := f2; mid12 := me12; mid21 := me21 |} =>
      (fun _ f2 _ _ T (H : E1 T) => f2 T (inl1 H)) f1 f2 me12 me21
    end.

  Definition RSub : E2 -< E :=
    match EE with
     {| mfun1 := f1; mfun2 := f2; mid12 := me12; mid21 := me21 |} =>
      (fun _ f2 _ _ T (H : E2 T) => f2 T (inr1 H)) f1 f2 me12 me21
    end.

End ProjAux.

  Notation cutoff EE e := (@subevent _ _ (RSub EE) _ e).
  
  Notation effect EE e := (@subevent _ _ (LSub EE) _ e).

  Notation Cutoff EE e :=
    (exists e0, e = cutoff EE e0).

  Notation Effect EE e :=
    (exists e0, e = effect EE e0).

  Notation DoCutoffF EE t := 
   (exists T (e: _ T) k, t = VisF (cutoff EE e) k).

  Notation DoCutoff EE t := (DoCutoffF EE (observe t)).

  Notation DoEffectF EE t := 
   (exists T (e: _ T) k, t = VisF (effect EE e) k).

  Notation DoEffect EE t := (DoEffectF EE (observe t)).

  Notation WillCutoff EE t := 
    (exists T (e: _ T) k,
      @eutt _ _ _ eq t (Vis (cutoff EE e) k)).
  
Section ProjLemmas.
  Context {E: Type -> Type}.
  Context {E1: Type -> Type}.
  Context {E2: Type -> Type}.
  Context (EE : FIso E (E1 +' E2)).

  Lemma IsoInjection1: forall T (e1 e2: E1 T),   
     effect EE e1 = effect EE e2 -> e1 = e2.    
  Proof.
    intros T e1 e2 H.
    unfold subevent, resum, RSub, LSub in H.
    destruct EE as [f1 f2 me1 me2].
    assert (f1 T (f2 T (inl1 e1)) = f1 T (f2 T (inl1 e2))) as A1.
    { rewrite H; auto. }
    repeat (rewrite me1 in A1).
    inv A1; auto.
  Qed.

  Lemma IsoInjection2: forall T (e1 e2: E2 T),   
     cutoff EE e1 = cutoff EE e2 -> e1 = e2.
  Proof.  
    intros T e1 e2 H.
    unfold subevent, resum, RSub, LSub in H.
    destruct EE as [f1 f2 me1 me2].
    assert (f1 T (f2 T (inr1 e1)) = f1 T (f2 T (inr1 e2))) as A1.
    { rewrite H; auto. }
    repeat (rewrite me1 in A1).
    inv A1; auto.
  Qed.
    
  Lemma IsoCongruence12: forall T (e1: E1 T) (e2: E2 T),   
      effect EE e1 = cutoff EE e2 -> False.
  Proof.  
    intros T e1 e2 H.
    unfold subevent, resum, RSub, LSub in H.
    destruct EE as [f1 f2 me1 me2].
    assert (f1 T (f2 T (inl1 e1)) = f1 T (f2 T (inr1 e2))) as A1.
    { rewrite H; auto. }
    repeat (rewrite me1 in A1).
    inv A1.
  Qed.

  Lemma IsoCongruence21: forall T (e1: E1 T) (e2: E2 T),   
      cutoff EE e2 = effect EE e1 -> False.
  Proof.  
    intros T e1 e2 H.
    symmetry in H.
    eapply IsoCongruence12; eauto.
  Qed.     

  Lemma Do2WillCutoff {R} (t: itree E R) :
    DoCutoff EE t -> WillCutoff EE t.
    intros [T [e [k H]]].
    exists T, e, k.
    setoid_rewrite itree_eta.
    setoid_rewrite H.
    simpl; reflexivity.
  Qed.  
  
End ProjLemmas.  


(** Loose Generalized Rutt ***********************************************)

Section RuttF.

  Context {E1 E2: Type -> Type}.
  Context {R1 R2 : Type}.
  Context {Ef1 Ef2: Type -> Type}.
  Context {Er1 Er2: Type -> Type}.
  Context (EE1 : FIso E1 (Ef1 +' Er1)).
  Context (EE2 : FIso E2 (Ef2 +' Er2)).

(* loose version: relations on all events *)  
  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
  Context (RR : R1 -> R2 -> Prop).
  
  Arguments REv {A} {B}.
  Arguments RAns {A} {B}.
    
  Inductive ruttF
    (sim : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree' E1 R1 -> itree' E2 R2 -> Prop :=
  | EqRet : forall (r1 : R1) (r2 : R2),
      RR r1 r2 ->
      ruttF sim (RetF r1) (RetF r2)
  | EqTau : forall (m1 : itree E1 R1)
                   (m2 : itree E2 R2),
      sim m1 m2 ->
      ruttF sim (TauF m1) (TauF m2)
  | EqVis : forall (A B : Type) (e1 : E1 A) (e2 : E2 B)
                   (k1 : A -> itree E1 R1)
                   (k2 : B -> itree E2 R2),
      REv e1 e2 ->
      (forall (a : A) (b : B), RAns e1 a e2 b -> sim (k1 a) (k2 b)) ->
      ruttF sim (VisF e1 k1) (VisF e2 k2)
  | EqErrL: forall A (e1 : Er1 A)
                   (k1: A -> itree E1 R1)
                   (ot2: itree' E2 R2),  
      ruttF sim (VisF (@subevent _ _ (RSub EE1) _ e1) k1) ot2            
  | EqErrR: forall A (e2 : Er2 A)
                   (k2: A -> itree E2 R2)
                   (ot1: itree' E1 R1),  
      ruttF sim ot1 (VisF (@subevent _ _ (RSub EE2) _ e2) k2)             
  | EqTauL : forall (t1 : itree E1 R1)
                    (ot2 : itree' E2 R2),
      ruttF sim (observe t1) ot2 ->
      ruttF sim (TauF t1) ot2
  | EqTauR : forall (ot1 : itree' E1 R1)
                    (t2 : itree E2 R2),
      ruttF sim ot1 (observe t2) ->
      ruttF sim ot1 (TauF t2).  
  Hint Constructors ruttF : itree.

  Definition rutt_
    (sim : itree E1 R1 -> itree E2 R2 -> Prop)
    (t1 : itree E1 R1) (t2 : itree E2 R2) :=
    ruttF sim (observe t1) (observe t2).
  Hint Unfold rutt_ : itree.

  Lemma rutt_monot : monotone2 rutt_.
  Proof.
    red. intros. red; induction IN; eauto with itree.
  Qed.

  Definition rutt :
    itree E1 R1 -> itree E2 R2 -> Prop :=
    paco2 rutt_ bot2.
  Hint Unfold rutt : itree.

  Lemma ruttF_inv_VisF_r {sim} t1 U2 (ee2: E2 U2) (k2: U2 -> _):
    ruttF sim t1 (VisF ee2 k2) ->
    (exists U1 (ee1: E1 U1) k1,
        t1 = VisF ee1 k1 /\
        forall v1 v2, RAns ee1 v1 ee2 v2 -> sim (k1 v1) (k2 v2))
    \/
    DoCutoffF EE1 t1 
    \/
    Cutoff EE2 ee2 
    \/
    (exists t1', t1 = TauF t1' /\
                   ruttF sim (observe t1') (VisF ee2 k2)).        
  Proof.
    intros.
    remember t1 as t0.
    destruct t0.

    - dependent destruction H.
      right; right; left; eauto.

    - dependent destruction H.
      + right; right; left; eauto.
      + repeat right; eauto.

    - dependent destruction H.
      + left; eauto.
      + right; left; eauto.
      + right; right; left; eauto.  
  Qed.
  
  Lemma ruttF_inv_VisF {sim} U1 U2
    (ee1 : E1 U1) (ee2 : E2 U2)
    (k1 : U1 -> itree E1 R1) (k2 : U2 -> itree E2 R2) :
      ruttF sim (VisF ee1 k1) (VisF ee2 k2) ->
      (forall v1 v2, RAns ee1 v1 ee2 v2 -> sim (k1 v1) (k2 v2))
      \/
        Cutoff EE1 ee1 
      \/
        Cutoff EE2 ee2.
  Proof.
    intros H. dependent destruction H; eauto. 
  Qed.
  
  Ltac unfold_rutt :=
    (try match goal with [|- rutt_ _ _ _ _ _ _ _ _ _ _ _ _ _ ] => red end);
    (repeat match goal with [H: rutt_ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] =>
                              red in H end).

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

Check @rutt.

Tactic Notation "fold_ruttF" hyp(H) :=
  try punfold H;
  try red in H;
  match type of H with
  | ruttF ?_REV ?_RANS ?_RR (upaco2 (rutt_ ?_REV ?_RANS ?_RR) bot2)
      ?_OT1 ?_OT2 =>
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
  Context {E1 E2: Type -> Type}.
  Context {R1 R2 : Type}.
  Context {Ef1 Ef2: Type -> Type}.
  Context {Er1 Er2: Type -> Type}.
  Context {EE1 : FIso E1 (Ef1 +' Er1)}.
  Context {EE2 : FIso E2 (Ef2 +' Er2)}.

(* loose version: relations on all events *)  
  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
  Context (RR : R1 -> R2 -> Prop).
  
Lemma rutt_Ret r1 r2:
  RR r1 r2 ->
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR 
    (Ret r1: itree E1 R1) (Ret r2: itree E2 R2).
Proof. intros. pstep; constructor; auto. Qed.

Lemma rutt_inv_Ret r1 r2:
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR (Ret r1) (Ret r2) ->
  RR r1 r2.
Proof.
  intros. punfold H. inv H. eauto.
Qed.

Lemma rutt_inv_Ret_l r1 t2:
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR (Ret r1) t2 ->
  (exists r2, t2 ≳ Ret r2 /\ RR r1 r2) \/ (WillCutoff EE2 t2).
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2).
  remember (RetF r1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate.
  - left. inversion Heqot1; subst. exists r2. split; [reflexivity|auto].
  - right. exists A, e2, k2. reflexivity.     
  - destruct (IHHrutt Heqot1) as [[r2 [H1 H2]] | H1].
    + left; exists r2; split; auto.
      rewrite <- itree_eta in H1. now rewrite tau_euttge.
    + right.
      destruct H1 as [T [e0 [k0 H1]]].
      exists T, e0, k0.
      setoid_rewrite <- H1.
      setoid_rewrite <- itree_eta.
      eapply tau_eutt.
Qed.      

Lemma rutt_inv_Ret_r t1 r2:
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR t1 (Ret r2) ->
  (exists r1, t1 ≳ Ret r1 /\ RR r1 r2) \/ (WillCutoff EE1 t1).
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (RetF r2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate.
  - left. inversion Heqot2; subst. exists r1. split; [reflexivity|auto].
  - right. exists A, e1, k1. reflexivity.      
  - destruct (IHHrutt Heqot2) as [[r1 [H1 H2]] | H].
    + left. exists r1; split; auto.
      rewrite <- itree_eta in H1. now rewrite tau_euttge.
    + right.
      destruct H as [T [e0 [k0 H1]]].
      exists T, e0, k0.
      setoid_rewrite <- H1.
      setoid_rewrite <- itree_eta.
      eapply tau_eutt.      
Qed.

(**)

Lemma break_inv_l t1 t2 :
  DoCutoff EE1 t1 ->
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros [T [e0 [k0 H1]]].
  pcofix CIH.
  pstep; red.
  rewrite H1.
  econstructor.
Qed.  

Lemma break_inv_r t1 t2 :
  DoCutoff EE2 t2 ->
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros [T [e0 [k0 H1]]].
  pcofix CIH.
  pstep; red.
  rewrite H1.
  econstructor.
Qed.  

Lemma rutt_inv_Tau_l t1 t2 :
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR (Tau t1) t2 ->
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  remember (TauF t1) as tt1. genobs t2 ot2.
  hinduction H before t1; intros; try discriminate.
  - inv Heqtt1. pclearbot. pstep. red. simpobs. econstructor; eauto.
    pstep_reverse.
  - assert (DoCutoff EE2 t2) as A1.
    { rewrite <- Heqot2; eauto. }
    eapply break_inv_r; auto.
  - inv Heqtt1. punfold_reverse H.
  - red in IHruttF. pstep. red; simpobs. econstructor; eauto. pstep_reverse.
Qed.
  
Lemma rutt_add_Tau_l t1 t2 :
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR t1 t2 ->
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR (Tau t1) t2.
Proof.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma rutt_inv_Tau_r t1 t2 :
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR t1 (Tau t2) ->
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros. punfold H. red in H. simpl in *.
  pstep. red. remember (TauF t2) as tt2 eqn:Ett2 in H.
  revert t2 Ett2.
  induction H; try discriminate; intros; inversion Ett2; subst; auto.
  - pclearbot. constructor. pstep_reverse.
  - constructor; auto.
  - constructor. eapply IHruttF; eauto.
Qed.

Lemma rutt_add_Tau_r t1 t2 :
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR t1 t2 ->
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR t1 (Tau t2).
Proof.
  intros. pfold. red. cbn. constructor. pstep_reverse.
Qed.

Lemma rutt_inv_Tau t1 t2 :
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR (Tau t1) (Tau t2) ->
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR t1 t2.
Proof.
  intros; apply rutt_inv_Tau_r, rutt_inv_Tau_l; assumption.
Qed.

(**)

Lemma rutt_Vis {T1 T2} (e1: E1 T1) (e2: E2 T2)
    (k1: T1 -> itree E1 R1) (k2: T2 -> itree E2 R2):
  REv _ _ e1 e2 ->
  (forall t1 t2, RAns _ _ e1 t1 e2 t2 ->
    @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR (k1 t1) (k2 t2)) ->
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR
    (Vis e1 k1) (Vis e2 k2).
Proof.
  intros He Hk. pstep; constructor; auto.
  intros; left. apply Hk; auto.
Qed.

Lemma rutt_inv_Vis_l {U1} (e1: E1 U1) k1 t2:
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR
    (Vis e1 k1) t2 ->
  (exists U2 (e2: E2 U2) k2,
    t2 ≈ Vis e2 k2 /\
    REv _ _ e1 e2 /\
      (forall v1 v2, RAns _ _ e1 v1 e2 v2 ->
                     @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR
                       (k1 v1) (k2 v2)))
   \/ Cutoff EE1 e1 
   \/ WillCutoff EE2 t2.
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t2). remember (VisF e1 k1) as ot1; revert Heqot1.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot1; subst A. inversion_sigma; rewrite <- eq_rect_eq in *;
      subst; rename B into U2.
    repeat left.
    exists U2, e2, k2; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H0 v1 v2 HAns). red in H0. now pclearbot.
  - dependent destruction Heqot1.
    right. left. econstructor; reflexivity. 
  - repeat right.
    econstructor. exists e2, k2. reflexivity.
  - destruct (IHHrutt eq_refl) as [[U2 [e2 [k2 [Ht0 HAns]]]] | H].
    + left.
      rewrite <- itree_eta in Ht0.
      exists U2, e2, k2; split; auto. now rewrite tau_eutt.
    + right. 
      destruct H as [H | H]; auto.
      right; destruct H as [T [e0 [k0 H0]]].
      exists T, e0, k0.
      eapply eqit_Tau_l.
      rewrite itree_eta; auto.
Qed.

(**)

Lemma rutt_inv_Vis_r {U2} t1 (e2: E2 U2) k2:
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR
    t1 (Vis e2 k2) ->
  (exists U1 (e1: E1 U1) k1,
    t1 ≈ Vis e1 k1 /\
    REv U1 U2 e1 e2 /\
     (forall v1 v2, RAns _ _ e1 v1 e2 v2 ->
                    @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR
                      (k1 v1) (k2 v2)))
   \/ Cutoff EE2 e2 
   \/ WillCutoff EE1 t1.
Proof.
  intros Hrutt; punfold Hrutt; red in Hrutt; cbn in Hrutt.
  setoid_rewrite (itree_eta t1). remember (VisF e2 k2) as ot2; revert Heqot2.
  induction Hrutt; intros; try discriminate; subst.
  - inversion Heqot2; subst B. inversion_sigma; rewrite <- eq_rect_eq in *;
      subst; rename A into U1.
    repeat left.
    exists U1, e1, k1; split. reflexivity. split; auto.
    intros v1 v2 HAns. specialize (H0 v1 v2 HAns). red in H0. now pclearbot.
  - repeat right.
    econstructor. exists e1, k1. reflexivity.
  - dependent destruction Heqot2.
    right. left. econstructor; reflexivity. 
  - destruct (IHHrutt eq_refl) as [[U1 [e1 [k1 [Ht0 HAns]]]] | H].
    + left.
      rewrite <- itree_eta in Ht0.
      exists U1, e1, k1; split; auto. now rewrite tau_eutt.
    + right. 
      destruct H as [H | H]; auto.
      right; destruct H as [T [e0 [k0 H0]]].
      exists T, e0, k0.
      eapply eqit_Tau_l.
      rewrite itree_eta; auto.
Qed.

Lemma rutt_inv_Vis U1 U2 (e1: E1 U1) (e2: E2 U2)
    (k1: U1 -> itree E1 R1) (k2: U2 -> itree E2 R2):
  @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR
    (Vis e1 k1) (Vis e2 k2) ->
  (forall u1 u2, RAns U1 U2 e1 u1 e2 u2 ->
     @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 REv RAns RR (k1 u1) (k2 u2))
   \/ Cutoff EE1 e1 
   \/ Cutoff EE2 e2. 
Proof.
  intro H. punfold H. red in H.
  apply ruttF_inv_VisF in H.
  destruct H; auto.
  left. intros u1 u2 Hans.
  eapply H in Hans.
  pclearbot; auto.
Qed.  
End ConstructionInversion.


(************************************************************)

Section euttge_trans_clo.

  Context {E1 E2: Type -> Type}.
  Context {R1 R2 : Type}.
  Context {Ef1 Ef2: Type -> Type}.
  Context {Er1 Er2: Type -> Type}.
  Context (EE1 : FIso E1 (Ef1 +' Er1)).
  Context (EE2 : FIso E2 (Ef2 +' Er2)).

  Context (RR : R1 -> R2 -> Prop).
  
  (* Closing a relation over itrees under [euttge].
     Essentially the same closure as [eqit_trans_clo], but heterogeneous
     in the interface argument [E].
     We only define the closure under [euttge] as opposed to [eqit_trans_clo]
     capturing closure under [eq_itree] and [eutt] at the same time, since it's
     the only one we need.
   *)

  (* A transitivity functor *)

  Variant euttge_trans_clo (r : itree E1 R1 -> itree E2 R2 -> Prop) :
    itree E1 R1 -> itree E2 R2 -> Prop :=
   | eqit_trans_clo_intro t1 t2 t1' t2' RR1 RR2
                     (EQVl: euttge RR1 t1 t1')
                     (EQVr: euttge RR2 t2 t2')
                     (REL: r t1' t2')
                     (LERR1: forall x x' y, RR1 x x' -> RR x' y -> RR x y)
                     (LERR2: forall x y y', RR2 y y' -> RR x y' -> RR x y) :
      euttge_trans_clo r t1 t2
    | eqit_trans_clo_lcut_intro {T} (e: Er1 T)  k (t1: itree E1 R1) t2
        (OE: observe t1 = VisF (cutoff EE1 e) k) :
      euttge_trans_clo r t1 t2
    | eqit_trans_clo_rcut_intro {T} (e: Er2 T)  k t1 (t2: itree E2 R2)
        (OE: observe t2 = VisF (cutoff EE2 e) k) :
      euttge_trans_clo r t1 t2.
  Hint Constructors euttge_trans_clo : itree.

  Lemma euttge_trans_clo_mon r1 r2 t1 t2
        (IN : euttge_trans_clo r1 t1 t2)
        (LE : r1 <2= r2) :
    euttge_trans_clo r2 t1 t2.
  Proof.
    destruct IN. econstructor; eauto.
    econstructor 2; eauto.
    econstructor 3; eauto.
  Qed.

  Hint Resolve euttge_trans_clo_mon : paco.

End euttge_trans_clo.

(*replicate this proof for the models functor*)
(* Validity of the up-to [euttge] principle *)
Lemma euttge_trans_clo_wcompat E1 E2 R1 R2 Ef1 Ef2 Er1 Er2
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2))
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  (RR : R1 -> R2 -> Prop) :
  wcompatible2 (rutt_ EE1 EE2 REv RAns RR) (euttge_trans_clo EE1 EE2 RR).
Proof.
  constructor; eauto with paco.
  { red. intros. eapply euttge_trans_clo_mon; eauto. }
  intros.
  destruct PR.

  2: { red. rewrite OE. econstructor; auto. }
  2: { red. rewrite OE. econstructor; auto. }
  
  punfold EQVl. punfold EQVr. unfold_eqit.
  hinduction REL before r; intros; clear t1' t2'.
  - remember (RetF r1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto;
      (try constructor; eauto).
    remember (RetF r3) as x. hinduction EQVr before r; intros; subst;
      try inv Heqx; (try constructor; eauto).
  - red. remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK;
      ( try (constructor; eauto; fail )).
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK;
      (try (constructor; eauto; fail)).
    pclearbot. constructor. gclo. econstructor; eauto with paco.
  - remember (VisF e1 k1) as x. red.
    hinduction EQVl before r; intros; subst; try discriminate;
      try (constructor; eauto; fail).
    remember (VisF e2 k3) as y.
    hinduction EQVr before r; intros; subst; try discriminate;
      try (constructor; eauto; fail).
    dependent destruction Heqx.
    dependent destruction Heqy.
    constructor; auto. intros. apply H0 in H1. pclearbot.
    apply gpaco2_clo.
    econstructor; eauto with itree.
  - remember (VisF (cutoff EE1 e1) k1) as x. red.
    hinduction EQVl before r; intros; subst; try discriminate;
      try (constructor; eauto; fail).
    dependent destruction Heqx.
    constructor; eauto.
  - remember (VisF (cutoff EE2 e2) k2) as x. red.
    hinduction EQVr before r; intros; subst; try discriminate;
      try (constructor; eauto; fail).
    dependent destruction Heqx.
    constructor; eauto.
  - remember (TauF t1) as x. red.
    hinduction EQVl before r; intros; subst; try inv Heqx;
      try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
  - remember (TauF t2) as y. red.
    hinduction EQVr before r; intros; subst; try inv Heqy;
      try inv CHECK; (try (constructor; eauto; fail)).
    pclearbot. punfold REL. constructor. eapply IHREL; eauto.
Qed.


#[global] Hint Resolve euttge_trans_clo_wcompat : paco.

(* The validity of the up-to [euttge] entails we can rewrite under [euttge]
   and hence also [eq_itree] during coinductive proofs of [rutt]
 *)
#[global] Instance grutt_cong_eqit {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2))
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RS : R1 -> R2 -> Prop}
  {RR1 RR2} r rg
  (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
  (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
  Proper (eq_itree RR1 ==> eq_itree RR2 ==> flip impl)
    (gpaco2 (rutt_ EE1 EE2 REv RAns RS)
       (euttge_trans_clo EE1 EE2 RS) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto;
    try eapply eqit_mon; try apply H; try apply H0; auto.
Qed.
  
Global Instance grutt_cong_euttge {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2))
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RS : R1 -> R2 -> Prop}
  {RR1 RR2} r rg
  (LERR1: forall x x' y, (RR1 x x': Prop) -> (RS x' y: Prop) -> RS x y)
  (LERR2: forall x y y', (RR2 y y': Prop) -> RS x y' -> RS x y) :
  Proper (euttge RR1 ==> euttge RR2 ==> flip impl)
    (gpaco2 (rutt_ EE1 EE2 REv RAns RS)
       (euttge_trans_clo EE1 EE2 RS) r rg).
Proof.
  repeat intro. gclo. econstructor; eauto.
Qed.

(* Provide these explicitly since typeclasses eauto cannot infer them *)

#[global] Instance grutt_cong_eqit_eq {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2))
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RS : R1 -> R2 -> Prop}
  r rg :
    Proper (eq_itree eq ==> eq_itree eq ==> flip impl)
      (gpaco2 (rutt_ EE1 EE2 REv RAns RS)
         (euttge_trans_clo EE1 EE2 RS) r rg).
Proof.
  apply grutt_cong_eqit; now intros * ->.
Qed.

#[global] Instance grutt_cong_euttge_eq {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2))
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RS : R1 -> R2 -> Prop}
  r rg :
    Proper (euttge eq ==> euttge eq ==> flip impl)
      (gpaco2 (rutt_ EE1 EE2 REv RAns RS)
         (euttge_trans_clo EE1 EE2 RS) r rg).
Proof.
  apply grutt_cong_euttge; now intros * ->.
Qed.


