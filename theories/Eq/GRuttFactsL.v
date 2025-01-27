(** * Properties about rutt *)

(** [rutt] retains most of the structure of [eutt], including being an
  equivalence relation, inversion lemmas, and compatibility with [eq_itree] and
  [euttge]. *)

(** The main additions in this file are compatibility with [eutt], morphisms
  wrt. [REv] and [RAns], and an up-to principle. *)

From Coq Require Import
  Program
  Setoid
  Morphisms
  RelationClasses.

From Paco Require Import
  paco.

From ITree Require Import
  ITree
  ITreeFacts
  Core.Subevent
  Basics.HeterogeneousRelations
  Eq.GRuttL
  Props.Leaf.

(* Morphisms related to [REv] and [RAns]. Both behave nicely up to quantified
   relation equality. There are also symmetry results when flipped.
*)

Definition eq_tfun (E1 E2: Type -> Type) : Prop :=
  forall A, E1 A = E2 A.

Global Instance subsum_eq_Proper :
  Proper (eq_tfun ==> eq_tfun ==> eq) (fun X Y => X -< Y).
Proof.
  unfold Proper, eq_tfun, respectful, ReSum, IFun; simpl.
  intros x y H x0 y0 H0.
  assert (forall T : Type, (x T -> x0 T) = (y T -> y0 T)) as A1.
  { intro T; rewrite <- H0.
    rewrite <- H; auto. }  
  set (F1 := fun t => x t -> x0 t).
  set (F2 := fun t => y t -> y0 t).
  assert (forall T, F1 T = F2 T) as A2.
  { subst F1 F2. simpl; auto. }
  eapply (@forall_extensionality Type F1 F2) in A1; auto.
Qed.

Global Instance FIso_Proper :
  Proper (eq_tfun ==> eq_tfun ==> eq) FIso.
Proof.
  unfold Proper, eq_tfun, respectful, ReSum, IFun; simpl.
  intros x y H x0 y0 H0.
  eapply functional_extensionality in H; auto.
  eapply functional_extensionality in H0; auto.
  inv H; auto.
Qed.  

(* We can't use eq_rel directly due to dependent quantification *)
Definition eq_REv {E1 E2: Type -> Type}
  (REv1 REv2 : forall A B, E1 A -> E2 B -> Prop) : Prop := 
  forall A B, eq_rel (REv1 A B) (REv2 A B).

#[global] Instance eq_REv_Equivalence {E1 E2} : Equivalence (@eq_REv E1 E2).
Proof.
  constructor.
  - red. red. reflexivity.
  - red. intros * H. red in H. red. now symmetry.
  - hnf. intros * H1 H2. red in H1, H2. red. etransitivity; eauto.
Qed.

Definition flip_REv {E1 E2: Type -> Type}
  (REv1: forall A B, E1 A -> E2 B -> Prop) :=
  fun B A e2 e1 => REv1 A B e1 e2.

Lemma flip_flip_REv {E1 E2} REv1:
  @eq_REv E1 E2 (flip_REv (flip_REv REv1)) REv1.
Proof. reflexivity. Qed.

(* For RAns we want to defer to eq_rel, but for that we need to regroup events
   and their return values into pairs.
*)
Definition RAns_pair E1 E2 (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop)
  {A B}:
    relationH (E1 A * A) (E2 B * B) :=
  fun '(e1, a) '(e2, b) => RAns A B e1 a e2 b.

Lemma RAns_pair_iff {E1 E2 A B} RAns1:
  forall e1 (a:A) e2 (b:B),
    RAns_pair E1 E2 RAns1 (e1,a) (e2,b) <-> RAns1 A B e1 a e2 b.
Proof. reflexivity. Qed.

Definition eq_RAns {E1 E2}
  (RAns1 RAns2: forall A B, E1 A -> A -> E2 B -> B -> Prop) :=
  forall A B, eq_rel (@RAns_pair E1 E2 RAns1 A B) (@RAns_pair E1 E2 RAns2 A B).

Lemma eq_RAns_iff {E1 E2} {RAns1 RAns2} (H: @eq_RAns E1 E2 RAns1 RAns2):
  forall A B e1 a e2 b, RAns2 A B e1 a e2 b <-> RAns1 A B e1 a e2 b.
Proof. intros *. rewrite <- ! RAns_pair_iff. split; apply H. Qed.

#[global] Instance eq_RAns_Equivalence {E1 E2}: Equivalence (@eq_RAns E1 E2).
Proof.
  constructor.
  - red; red. reflexivity.
  - red; red. now symmetry.
  - red; red. intros * H1 H2. red in H1, H2. etransitivity; eauto.
Qed.

Definition flip_RAns {E1 E2}
  (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop) :=
  fun B A e2 (b:B) e1 (a:A) =>
    flip (@RAns_pair E1 E2 RAns A B) (e2, b) (e1, a).

Lemma flip_RAns_iff {E1 E2 A B} RAns:
  forall e1 (a:A) e2 (b:B), @flip_RAns E1 E2 RAns B A e2 b e1 a <->
                              RAns _ _ e1 a e2 b.
Proof. reflexivity. Qed.

Lemma flip_flip_RAns {E1 E2}
  (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop):
  eq_RAns (flip_RAns (flip_RAns RAns)) RAns.
Proof. reflexivity. Qed.


(* Extra construction lemmas ******************************************)

Lemma rutt_trigger {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2))
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop)
  {RR : R1 -> R2 -> Prop} 
  (e1: E1 R1) (e2: E2 R2) : 
  (REv _ _ e1 e2: Prop) -> 
  (forall t1 t2, (RAns _ _ e1 t1 e2 t2: Prop) -> (RR t1 t2: Prop)) -> 
  rutt EE1 EE2 REv RAns RR (trigger e1) (trigger e2).
Proof.
  intros. apply rutt_Vis; auto.
  intros. apply rutt_Ret; auto.
Qed.
       
Lemma rutt_flip {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2))
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RR : R1 -> R2 -> Prop} 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  rutt EE1 EE2 REv RAns RR t1 t2 <->
    rutt EE2 EE1 (flip_REv REv) (flip_RAns RAns) (flip RR) t2 t1.
Proof.
  split; revert t1 t2; pcofix CIH; intros t1 t2 Hrutt;
  punfold Hrutt; red in Hrutt; pstep; red.
  - induction Hrutt; try now constructor.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. auto. intros b a HAns. cbn in HAns. right.
      specialize (H0 a b HAns). apply CIH. now pclearbot.
  - induction Hrutt; try now constructor.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. auto. intros b a HAns. cbn in HAns. right.
      specialize (H0 a b HAns). apply CIH. now pclearbot.
Qed.

(* Progressive [Proper] instances for [rutt] and congruence with eutt. *)

#[global] Instance rutt_Proper_R {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2)) :
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)       
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq             (* t1 *)
      ==> eq             (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2).
Proof.
  intros REv1 REv2 HREv RAns1 RAns2 HRAns RR1 RR2 HRR
         t1 _ <- t2 _ <-.
  split; intros Hrutt.
  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto using EqTauL, EqTauR.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. now apply HREv. intros.
      assert (H2: RAns1 A B e1 a e2 b).
      { erewrite <- eq_RAns_iff. apply H1. assumption. }
      intros. specialize (H0 a b H2). red. right. apply CIH.
      red in H0. now pclearbot.
    * apply EqCutL. 
    * apply EqCutR.
      
  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto using EqTauL, EqTauR.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis. now apply HREv. intros.
      assert (H2: RAns2 A B e1 a e2 b).
      { erewrite eq_RAns_iff. apply H1. assumption. }
      intros. specialize (H0 a b H2). red. right. apply CIH.
      red in H0. now pclearbot.
    * apply EqCutL.
    * apply EqCutR.  
Qed.

#[global] Instance rutt_Proper_R2 {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2)) :
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq_itree eq    (* t1 *)
      ==> eq_itree eq    (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2).
Proof.
  clear. intros REv1 REv2 HREv RAns1 RAns2 HRAns RR1 RR2 HRR
           t1 t1' Ht1 t2 t2' Ht2.
  split; intros Hrutt.

  - rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
    ginit. gclo. econstructor; eauto with paco.
    * symmetry in Ht1. apply eq_sub_euttge in Ht1. apply Ht1.
    * symmetry in Ht2. apply eq_sub_euttge in Ht2. apply Ht2.
    * intros. inv H; auto.
    * intros. inv H; auto.

  - rewrite HREv, HRAns, HRR; clear HREv REv1 HRAns RAns1 HRR RR1.
    ginit. gclo. econstructor; eauto with paco.
    * apply eq_sub_euttge in Ht1. apply Ht1.
    * apply eq_sub_euttge in Ht2. apply Ht2.
    * intros. inv H; auto.
    * intros. inv H; auto.  
Qed.

Lemma rutt_cong_eutt {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2)) :
  forall REv RAns RR
         (t1: itree E1 R1) t1' (t2: itree E2 R2),
  rutt EE1 EE2 REv RAns RR t1 t2 ->
  t1 ≈ t1' ->
  rutt EE1 EE2 REv RAns RR t1' t2.
Proof.
  (* First by coinduction; then do an induction on Hrutt to expose the ruttF
     linking t1 and t2; then an induction on Heutt to expose the relation
     between t1 and t1'. Finally, explore ruttF until landing on an rutt where
     the t1/t1' relation can be substituted by CIH, and conclude. *)
  intros * Hrutt Heutt; revert t1 t1' Heutt t2 Hrutt.
  ginit; gcofix CIH; intros t1 t1' Heutt t2 Hrutt.
  punfold Hrutt; red in Hrutt.
  
  rewrite (itree_eta t1) in Heutt.
  rewrite (itree_eta t2).
  
  move Hrutt before CIH. revert_until Hrutt.
  induction Hrutt as [ r1 r2 | m1 m2 | | | | m1 ot2 | ot1 m2 ];
    clear t1 t2; intros t1' Heutt.

  (* EqRet: t1 = Ret r1 ≈ t1'; we can rewrite away the Taus with the euttge
     closure and finish immediately with EqRet. *)
  - apply eutt_inv_Ret_l in Heutt. rewrite Heutt.
    (* gstep. apply EqRet; auto. *)
    gfinal; right; pstep. now apply EqRet.

  (* EqTau: The hardest case. When Heutt is EqTauL then we lack information to
     proceed, which requires that [desobs m1]. We then have to restart
     analyzing based on m1; the Ret case repeats EqRet above, while the Vis
     case repeats EqVis below. *)
  - punfold Heutt; red in Heutt; cbn in Heutt.
    rewrite itree_eta. pclearbot. fold_ruttF H.
    remember (TauF m1) as ot1; revert m1 m2 H Heqot1.
    induction Heutt as [|m1_bis m1'| |m1_bis ot1' _|t1_bis m1'];
    intros * Hrutt Heqot1; clear t1'; try discriminate.
    + inv Heqot1. pclearbot. gfinal; right; pstep; red.
      apply EqTau. right. now apply (CIH m1).
    + inv Heqot1. rewrite (itree_eta m1) in Hrutt.      
      desobs m1 Hm1; clear m1 Hm1.
      { fold_eqitF Heutt. apply eutt_inv_Ret_l in Heutt.
        rewrite Heutt, tau_euttge. gfinal; right. eapply paco2_mon_bot; eauto. }
      { apply rutt_inv_Tau_l in Hrutt. eapply IHHeutt; eauto. }
      { clear IHHeutt. remember (VisF e k) as m1; revert Heqm1.
        induction Heutt as [| |U1 e1 k1 k1' Hk1k1'| |]; intros;
          try discriminate.        
        - symmetry in Heqm1; dependent destruction Heqm1.
          rewrite tau_euttge, (itree_eta m2).
          punfold Hrutt; red in Hrutt; cbn in Hrutt.
          remember (VisF e1 k1) as m1; revert Heqm1.
          induction Hrutt; intros; try discriminate.
          * dependent destruction Heqm1.
            gfinal; right. pstep; red; cbn.
            apply EqVis; auto. intros v1 v2 HAns. specialize (H0 v1 v2 HAns).
            hnf in H0; hnf. pclearbot; right. apply (CIH (k1 v1)); auto.
            apply Hk1k1'.
          * dependent destruction Heqm1.
            gstep. apply EqCutL; auto.
          * gstep. apply EqCutR; auto.
          * idtac. rewrite tau_euttge, (itree_eta t2). now apply IHHrutt.
        - idtac. rewrite tau_euttge, itree_eta; now apply IHHeutt. }
    + inv Heqot1. gfinal; right. pstep; red. apply EqTau. right.
      fold_eqitF Heutt. rewrite tau_euttge in Heutt. now apply (CIH m1).

  (* EqVis: Similar to EqRet, but we don't have t1' ≳ Vis e1 k1 because the
     continuations are "only" ≈. The up-to-eutt principle that enforces Vis
     steps could work, but we don't have it for rutt. Instead we peel the Tau
     layers off t1' with a manual induction. *)
  - rewrite itree_eta. gfinal; right; pstep.
    rename H0 into HAns. punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e1 k1) as m1; revert Heqm1.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm1.
      apply EqVis; auto. intros a b HAns'. specialize (HAns a b HAns').      
      hnf in HAns; hnf. pclearbot; right. apply (CIH (k1 a)); auto. apply REL.
    + (* eapply EqTauL. eapply IHHeutt. auto. *)
      now apply EqTauL, IHHeutt.      
  - rewrite itree_eta. gfinal; right; pstep.
     
    remember (VisF (cutoff EE1 e1) k1) as m1; revert Heqm1.
    punfold Heutt; red in Heutt; cbn in Heutt.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm1.
      apply EqCutL; auto.
    + apply EqTauL. eapply IHHeutt; auto.
    
  - gstep; red. econstructor; auto.
    
  (* EqTauL: We get a very strong IHHrutt at the ruttF level, which we can
     apply immediately; then handle the added Tau in ≈, which is trivial. *)
  - apply IHHrutt. rewrite <- itree_eta. now rewrite <- tau_eutt.
    
  (* EqTauR: Adding a Tau on the side of t2 changes absolutely nothing to the
     way we rewrite t1, so we can follow down and recurse. *)
  - rewrite tau_euttge. rewrite (itree_eta m2). now apply IHHrutt.
Qed.    
    
#[global] Instance rutt_Proper_R3 {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
  (EE1 : FIso E1 (Ef1 +' Er1))
  (EE2 : FIso E2 (Ef2 +' Er2)) :
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eutt eq        (* t1 *)
      ==> eutt eq        (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2).
Proof.
  intros REv REv2 HREv RAns RAns2 HRAns RR RR2 HRR
         t1 t1' Ht1 t2 t2' Ht2.
  rewrite <- HREv, <- HRAns, <- HRR; clear HREv REv2 HRAns RAns2 HRR RR2.
  split; intros Hrutt.
  
  - eapply rutt_cong_eutt; eauto.    
    rewrite rutt_flip in *; eauto.
    rewrite rutt_flip in Hrutt; eauto.
    eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip; eauto.
    
  - symmetry in Ht1, Ht2.
    eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip in *; eauto.
    rewrite rutt_flip in Hrutt; eauto.
    eapply rutt_cong_eutt; eauto.
    rewrite rutt_flip; eauto.
Qed.

(* Bind closure and bind lemmas. *)

Section RuttBind.
  Context {E1 E2: Type -> Type}.
  Context {R1 R2 : Type}.
  Context {Ef1 Ef2: Type -> Type}.
  Context {Er1 Er2: Type -> Type}.
  Context (EE1 : FIso E1 (Ef1 +' Er1)).
  Context (EE2 : FIso E2 (Ef2 +' Er2)).

  Context (REv : forall (A B : Type), E1 A -> E2 B -> Prop).
  Context (RAns : forall (A B : Type), E1 A -> A -> E2 B -> B -> Prop).
  Context (RR : R1 -> R2 -> Prop).

Inductive rutt_bind_clo (r : itree E1 R1 -> itree E2 R2 -> Prop) :
  itree E1 R1 -> itree E2 R2 -> Prop :=
| rbc_intro_h U1 U2 (RU : U1 -> U2 -> Prop) t1 t2 k1 k2
      (EQV: rutt EE1 EE2 REv RAns RU t1 t2)
      (REL: forall u1 u2, RU u1 u2 -> r (k1 u1) (k2 u2))
  : rutt_bind_clo r (ITree.bind t1 k1) (ITree.bind t2 k2)
.
Hint Constructors rutt_bind_clo: core.

Lemma rutt_clo_bind :
  rutt_bind_clo <3= gupaco2 (rutt_ EE1 EE2 REv RAns RR)
                            (euttge_trans_clo EE1 EE2 RR).
Proof.
  intros rr. gcofix CIH. intros. destruct PR.
  gclo; econstructor; auto_ctrans_eq.
  1,2: rewrite unfold_bind; reflexivity.
  punfold EQV. unfold rutt_ in *.
  hinduction EQV before CIH; intros; pclearbot; cbn;
    repeat (change (ITree.subst ?k ?m) with (ITree.bind m k)).
  - gclo. econstructor; auto_ctrans_eq.
    1,2: reflexivity.
    eauto with paco.
  - gstep. econstructor. eauto 7 with paco.
  - gstep. econstructor; eauto 7 with paco.
    intros. specialize (H0 a b H1). pclearbot. eauto 7 with paco.
  - gstep. econstructor; auto.
  - gstep. econstructor; auto.  
  - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
  - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
Qed.

End RuttBind.

Lemma rutt_bind {E1 E2 R1 R2 Ef1 Ef2 Er1 Er2}
      (EE1 : FIso E1 (Ef1 +' Er1))
      (EE2 : FIso E2 (Ef2 +' Er2))
      (REv: forall A B, E1 A -> E2 B -> Prop)
      (RAns: forall A B, E1 A -> A -> E2 B -> B -> Prop)
      (RR: R1 -> R2 -> Prop)
      {T1 T2}
      (RT: T1 -> T2 -> Prop) t1 t2 k1 k2 :
    rutt EE1 EE2 REv RAns RR t1 t2 ->
    (forall r1 r2,
      RR r1 r2 ->
      rutt EE1 EE2 REv RAns RT (k1 r1) (k2 r2)) ->
    rutt EE1 EE2 REv RAns RT (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  intros. ginit.
  (* For some reason [guclo] fails, apparently trying to infer the type in a
     context with less information? *)
  eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco.
  econstructor; eauto. intros; subst. gfinal. right. apply H0. eauto.
Qed.

Section RuttMrec.
  Context {D1 D2 E1 E2 : Type -> Type}.
  Context {Ef1 Ef2: Type -> Type}.
  Context {Er1 Er2: Type -> Type}.

  Context (EE1 : FIso E1 (Ef1 +' Er1))
          (EE2 : FIso E2 (Ef2 +' Er2)).
            
  Context (RPre : prerel E1 E2) (RPreInv : prerel D1 D2)
          (RPost : postrel E1 E2) (RPostInv : postrel D1 D2).

  Context (bodies1 : D1 ~> itree (D1 +' E1))
          (bodies2 : D2 ~> itree (D2 +' E2)).
  
  Context (Hbodies : forall R1 R2 (d1 : D1 R1) (d2 : D2 R2), 
              RPreInv R1 R2 d1 d2 -> 
              @rutt (D1 +' E1) (D2 +' E2)
                R1 R2
                (D1 +' Ef1) (D2 +' Ef2) Er1 Er2
                (FIso_MR D1 EE1)
                (FIso_MR D2 EE2)               
                (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
                (fun (v1 : R1) (v2 : R2) =>
                   RPostInv R1 R2 d1 v1 d2 v2)
                     (bodies1 R1 d1) (bodies2 R2 d2) ).

  Lemma interp_mrec_rutt (R1 R2 : Type) (RR : R1 -> R2 -> Prop) :
    forall (t1 : itree (D1 +' E1) R1) (t2 : itree (D2 +' E2) R2),
      rutt (FIso_MR D1 EE1) (FIso_MR D2 EE2)
        (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
               RR t1 t2 -> 
      rutt EE1 EE2 RPre RPost
        RR (interp_mrec bodies1 t1) (interp_mrec bodies2 t2).
  Proof.
    ginit. gcofix CIH.
    intros t1 t2 Ht12. punfold Ht12. red in Ht12.
    remember (observe t1) as ot1. remember (observe t2) as ot2.
    hinduction Ht12 before r; intros.
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      gstep. red. cbn. constructor. auto.
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      repeat rewrite unfold_interp_mrec. cbn. gstep. constructor.
      pclearbot. gfinal. eauto.
    - apply simpobs in Heqot1, Heqot2. rewrite Heqot1, Heqot2.
      repeat rewrite unfold_interp_mrec. cbn.
      dependent destruction H.
      + remember (FIso_MR D1 EE1) as FI1.
        remember (FIso_MR D2 EE2) as FI2.
        set (H1 := FIso_MR_proj1 _ _ _ HeqFI1). 
        destruct FI1; simpl in *.
        set (H2 := FIso_MR_proj1 _ _ _ HeqFI2). 
        destruct FI2; simpl in *.
        gstep. constructor.
        gfinal. left. eapply CIH.
        eapply rutt_bind; eauto.
        intros. cbn in H3. clear - H3 H0.
        specialize (H0 r1 r2 (sum_postrel_inl _ _ _ _ _ _ _ _ H3)).
        pclearbot. auto.
      + (* unfold effect, resum, LSub. *)
        gstep. red. constructor; eauto.
        intros. 
        gstep. constructor.
        gfinal. left. eapply CIH.
        specialize (H0 a b (sum_postrel_inr _ _ _ _ _ _ _ _ H1)).
        pclearbot. eauto.
    - remember (FIso_MR D1 EE1) as FI1.
      set (H1 := FIso_MR_proj4 _ _ _ HeqFI1).
      destruct FI1; simpl in *.
      assert (GRuttL.mfun1 A (inr1 e1) = cutoff EE1 e1) as K1.
      { destruct EE1; simpl. eauto. }
      apply simpobs in Heqot1.
      rewrite Heqot1. 
      rewrite unfold_interp_mrec at 1. 
      cbn.
      setoid_rewrite H1.
      rewrite K1.
      gstep. red.
      econstructor.
    - remember (FIso_MR D2 EE2) as FI2.
      set (H1 := FIso_MR_proj4 _ _ _ HeqFI2).
      destruct FI2; simpl in *.
      assert (GRuttL.mfun1 A (inr1 e2) = cutoff EE2 e2) as K1.
      { destruct EE2; simpl. eauto. }
      apply simpobs in Heqot2.
      rewrite Heqot2. 
      setoid_rewrite unfold_interp_mrec at 2. 
      cbn.
      setoid_rewrite H1.
      rewrite K1.
      gstep. red.
      econstructor.      
    - apply simpobs in Heqot1. rewrite Heqot1.
      rewrite unfold_interp_mrec at 1. cbn.
      rewrite tau_euttge. auto.
    - apply simpobs in Heqot2. rewrite Heqot2.
      setoid_rewrite unfold_interp_mrec at 2.
      cbn. rewrite tau_euttge. auto.
  Qed.
  
  Lemma mrec_rutt (A B : Type) (d1 : D1 A) (d2 : D2 B) : 
    RPreInv A B d1 d2 ->
    rutt EE1 EE2 RPre RPost (fun (a : A) (b : B) => RPostInv A B d1 a d2 b) 
         (mrec bodies1 d1) (mrec bodies2 d2).
  Proof.
    intros. apply interp_mrec_rutt. auto.
  Qed.
 
End RuttMrec.


Section RuttIter.
  Context {E1 E2 : Type -> Type}.
  Context {Ef1 Ef2: Type -> Type}.
  Context {Er1 Er2: Type -> Type}.

  Context (EE1 : FIso E1 (Ef1 +' Er1))
          (EE2 : FIso E2 (Ef2 +' Er2)).

  Context (RPreE : forall A B : Type, E1 A -> E2 B -> Prop)
          (RPostE : forall A B : Type,
                         E1 A -> A -> E2 B -> B -> Prop).

  Context {I1 I2 R1 R2: Type}.
  
  Context (RI : I1 -> I2 -> Prop)
          (RR : R1 -> R2 -> Prop).

  Context (body1 : I1 -> itree E1 (I1 + R1))
          (body2 : I2 -> itree E2 (I2 + R2)).

Lemma rutt_iter :
  (forall j1 j2, RI j1 j2 ->
                 rutt EE1 EE2 RPreE RPostE
                   (sum_rel RI RR) (body1 j1) (body2 j2)) ->
  forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
    @rutt E1 E2 R1 R2 Ef1 Ef2 Er1 Er2 EE1 EE2 RPreE RPostE RR
      (ITree.iter body1 i1) (ITree.iter body2 i2). 
  ginit. gcofix CIH.
  intros.
  rewrite !unfold_iter.
  eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco.
  econstructor; eauto. intros; subst. gfinal. right.
  destruct u1; try discriminate.
  destruct u2; try discriminate.
  pstep; red.
  econstructor.
  right.
  eapply CIH; eauto.
  inversion H; subst; auto.
  pstep; red.
  inversion H; subst.
  destruct u2; try discriminate.
  inversion H; subst.
  pstep; red.
  econstructor.
  inversion H; subst; auto.
Qed.  

End RuttIter.

