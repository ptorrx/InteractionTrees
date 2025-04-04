(** * Properties about X-rutt *)

(** [X-rutt], like [rutt], retains most of the structure of [eutt].
    This is a simple refactoring of RuttFact.v, with an extra lemma
    about [iter]. *)

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
  Eq.YRutt (* Eq.YRutt3 *)
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


(* Specifically about [X-rutt] ******************************************)

Definition eq_RE {E: Type -> Type} {R: Type}
  (RE RE' : forall A, E A -> R -> Prop) : Prop := 
  forall A, eq_rel (RE A) (RE' A).

#[global] Instance eq_RE_Equivalence {E} {R}: Equivalence (@eq_RE E R).
Proof.
  constructor.
  - red; red. reflexivity.
  - red; red. now symmetry.
  - red; red. intros * H1 H2. red in H1, H2. etransitivity; eauto.
Qed.

(***)

Lemma rutt_trigger {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (ER1 : forall {X}, E1 X -> R2 -> Prop)
  (ER2 : forall {X}, E2 X -> R1 -> Prop)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop)
  {RR : R1 -> R2 -> Prop} 
  (e1: E1 R1) (e2: E2 R2) :
  (REv _ _ e1 e2: Prop) -> 
  (forall t1 t2, (RAns _ _ e1 t1 e2 t2: Prop) -> (RR t1 t2: Prop)) -> 
  rutt (@EE1) (@EE2) (@ER1) (@ER2) REv RAns RR (trigger e1) (trigger e2).
Proof.
  intros. apply rutt_Vis; auto.
  intros. apply rutt_Ret; auto.
Qed.
       
Lemma rutt_flip {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (ER1 : forall {X}, E1 X -> R2 -> Prop)
  (ER2 : forall {X}, E2 X -> R1 -> Prop)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RR : R1 -> R2 -> Prop} 
  (t1: itree E1 R1) (t2: itree E2 R2) :
  rutt (@EE1) (@EE2) (@ER1) (@ER2) REv RAns RR t1 t2 <->
    rutt (@EE2) (@EE1) (@ER2) (@ER1) 
      (flip_REv REv) (flip_RAns RAns) (flip RR) t2 t1.
Proof.
  split; revert t1 t2; pcofix CIH; intros t1 t2 Hrutt;
  punfold Hrutt; red in Hrutt; pstep; red.
  - induction Hrutt; try now constructor.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis; auto. intros b a HAns. cbn in HAns. right.
      specialize (H0 a b HAns). apply CIH. now pclearbot.
    * apply EqTauVis; auto. pclearbot. right. eapply CIH; auto.
    * apply EqVisTau; auto. pclearbot. right. eapply CIH; auto. 
  - induction Hrutt; try now constructor.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis; auto. intros b a HAns. cbn in HAns. right.
      specialize (H0 a b HAns). apply CIH. now pclearbot.
    * apply EqTauVis; auto. pclearbot. right. eapply CIH; auto.
    * apply EqVisTau; auto. pclearbot. right. eapply CIH; auto. 
Qed.

(* Progressive [Proper] instances for [X-rutt] and congruence with eutt. *)

#[global] Instance rutt_Proper_R {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool) :
  Proper (@eq_RE E1 R2    (* RE1 *)
      ==> @eq_RE E2 R1    (* RE2 *)          
      ==> eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)       
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq             (* t1 *)
      ==> eq             (* t2 *)
      ==> iff) (rutt EE1 EE2).
Proof.
  intros RE1 RE1' HRE1 RE2 RE2' HRE2
    REv1 REv2 HREv RAns1 RAns2 HRAns RR1 RR2 HRR
         t1 _ <- t2 _ <-.
  split; intros Hrutt.
  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto using EqTauL, EqTauR.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis; auto. now apply HREv. intros.
      assert (H4: RAns1 A B e1 a e2 b).
      { erewrite <- eq_RAns_iff. apply H1. assumption. } 
      intros. specialize (H0 a b H4). red. right. apply CIH.
      red in H0. now pclearbot.
    * apply EqVisRet; auto.
      eapply HRE1; auto.
    * apply EqRetVis; auto.
      eapply HRE2; auto.
    * apply EqVisTau; auto.
      pclearbot. simpl in *.
      red; right. apply CIH; auto.
    * apply EqTauVis; auto.
      pclearbot. simpl in *.
      red; right. apply CIH; auto.        
  - revert t1 t2 Hrutt; pcofix CIH; intros t1 t2 Hrutt.
    pstep. punfold Hrutt. red in Hrutt; red.
    hinduction Hrutt before CIH; intros; eauto using EqTauL, EqTauR.
    * apply EqRet. now apply HRR.
    * apply EqTau. right. apply CIH. now pclearbot.
    * apply EqVis; auto. now apply HREv. intros.
      assert (H4: RAns2 A B e1 a e2 b).
      { erewrite eq_RAns_iff. apply H1. assumption. }
      intros. specialize (H0 a b H4). red. right. apply CIH.
      red in H0. now pclearbot.
    * apply EqVisRet; auto.
      eapply HRE1; auto.
    * apply EqRetVis; auto.
      eapply HRE2; auto.
    * apply EqVisTau; auto.
      pclearbot. simpl in *.
      red; right. apply CIH; auto.
    * apply EqTauVis; auto.
      pclearbot. simpl in *.
      red; right. apply CIH; auto.        
Qed.

#[global] Instance rutt_Proper_R2 {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool) :
  Proper (@eq_RE E1 R2    (* RE1 *)
      ==> @eq_RE E2 R1    (* RE2 *)        
      ==> eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eq_itree eq    (* t1 *)
      ==> eq_itree eq    (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2 EE1 EE2).
Proof.
  clear. intros RE1 RE1' HRE1 RE2 RE2' HRE2
    REv1 REv2 HREv RAns1 RAns2 HRAns RR1 RR2 HRR
           t1 t1' Ht1 t2 t2' Ht2.
  split; intros Hrutt.

  - rewrite <- HREv, <- HRAns, <- HRR, <- HRE1, <- HRE2;
      clear HRE1 RE1' HRE2 RE2' HREv REv2 HRAns RAns2 HRR RR2.
    ginit. gclo. econstructor; eauto with paco.
    * symmetry in Ht1. apply eq_sub_euttge in Ht1. apply Ht1.
    * symmetry in Ht2. apply eq_sub_euttge in Ht2. apply Ht2.
    * intros. inv H0; auto.
    * intros. inv H0; auto. 
    * intros. inv H; auto.
    * intros. inv H; auto.
  - rewrite HREv, HRAns, HRR, HRE1, HRE2;
      clear HRE1 RE1 HRE2 RE2 HREv REv1 HRAns RAns1 HRR RR1.
    ginit. gclo. econstructor; eauto with paco.
    * apply eq_sub_euttge in Ht1. apply Ht1.
    * apply eq_sub_euttge in Ht2. apply Ht2.
    * intros. inv H0; auto.
    * intros. inv H0; auto.       
    * intros. inv H; auto.
    * intros. inv H; auto.  
Qed.

Lemma rutt_cong_eutt' {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool) 
  (ER1 : forall X, E1 X -> R2 -> Prop)
  (ER2 : forall X, E2 X -> R1 -> Prop) :
  forall REv RAns RR
         (t1 t1': itree E1 R1) (t2: itree E2 R2),
  t1 ≈ t1' ->    
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1' t2 ->
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 t2.
Proof.
  intros REv RAns RR. 
  pcofix CIH; intros t1 t1' t2 INL INR.
   
  punfold INL; punfold INR.
  red in INL; red in INR.
  pstep. red.
  remember (observe t2) as ot23.
  clear Heqot23 t2.

  hinduction INL before CIH; intros; subst. 
   
  (* 1 : ret1 ret2 *)  
  { remember (RetF r2) as ot2.
    hinduction INR before CIH; intros; inv Heqot2; eauto with paco itree.
    + eapply EqRet; eauto.
    + eapply EqRetVis; eauto.
    + constructor; eauto.   
  }

  (* 2: tau1 tau2 *)
  { pclearbot.
    assert (DEC: (exists m23, ot23 = TauF m23) \/
                   (forall m23, ot23 <> TauF m23)).
      { destruct ot23; eauto; right; red; intros; discriminate. }
      destruct DEC as [EQ | EQ].      
    + destruct EQ as [m23 ?]; subst.
      econstructor. right. pclearbot.
      eapply CIH; eauto with paco.
      eapply rutt_inv_Tau.
      eapply fold_ruttF; try eapply INR; eauto. 
    + assert (DEC1: ((exists A (e23: E2 A) k23, (ot23 = VisF e23 k23)
                             /\ IsCut_ EE2 A e23) \/
                      ((forall A (e23: E2 A) k23, ot23 <> VisF e23 k23)
                       \/ (exists A (e23: E2 A) k23, (ot23 = VisF e23 k23)
                             /\ NoCut_ EE2 A e23)))).
      { destruct ot23; eauto.
        right. left. intros. discriminate.
        right. left. intros. discriminate.
        assert (IsCut_ EE2 X e \/ NoCut_ EE2 X e) as D.
        { destruct (EE2 _ e). right; auto. left; auto. }
        destruct D.
        left. exists X, e, k. split; eauto.
        right. right. exists X, e, k. split; eauto. 
      }

      destruct DEC1 as [EQ1 | EQ1].
      destruct EQ1 as [A0 [e23 [k23 [A1 A2]]]].
      inv A1.
      dependent destruction INR; try (exfalso; eapply EQ; eauto; fail).
      
      * pclearbot. eapply EqTauVis; eauto.
      * eapply EqTauVis; eauto.
        pclearbot. punfold REL. red in REL.
        red. right.
        eapply CIH; eauto.
        instantiate (1:= m2).
        pstep; red. auto.
        pstep; red. auto.
      * inv INR; intros; try (exfalso; eapply EQ; eauto; fail).
        { destruct EQ1.
          specialize (H A e2 k2).
          contradiction.
          destruct H as [A0 [e23 [k23 [B0 B1]]]]. 
          dependent destruction B0.
          destruct (EE2 _ e23).
          inv H0.
          inv B1.
        }  
        
        eapply EqTauL; eauto. 
        pclearbot. punfold REL. red in REL.
        hinduction H0 before CIH; intros; try (exfalso; eapply EQ; eauto; fail).

      (* ret3 *)
      { remember (RetF r1) as ot2.  
        hinduction REL before CIH; intros; inv Heqot2; eauto with paco itree.
        + constructor; eauto. 
        + eapply EqTauL; eauto. }

      (* vis3 *)
      { remember (VisF e1 k1) as ot2.
        hinduction REL before CIH; intros; try discriminate.

        { dependent destruction Heqot2.
          constructor; eauto.
          
          intros a b H7.
          destruct (H0 _ _ H7), (REL a); try contradiction; eauto. 
        }    

        { eapply EqTauL; eauto. }
      }

      (* cut2 *)
      { clear EQ; remember (VisF e1 k1) as ot4.
        hinduction REL before CIH; intros; try discriminate.

        - dependent destruction Heqot4.
          eapply EqVisRet; eauto.
        - eapply EqTauL; eauto.  
      }

      { clear EQ; remember (RetF r1) as ot4.
        hinduction REL before CIH; intros; try discriminate.

        - dependent destruction Heqot4.
          eapply EqRetVis; eauto.
        - eapply EqTauL; eauto.  
      }    

      (* cut3 *)
      { clear EQ.

        remember (TauF m1) as ot4. (* remember m0 as ot3. *)        
        hinduction REL before CIH; intros; try discriminate.

        - dependent destruction Heqot4.
          eapply EqTauVis; eauto.
          red. right.
          pclearbot.
          eapply CIH; eauto.
        - pclearbot.
          eapply EqTauVis; eauto.
          red. right.
          eapply CIH; eauto.
          inv Heqot4.
          eapply eqit_inv_Tau_r.
          pstep; red. auto.

        - dependent destruction Heqot4.
          pclearbot.
          destruct EQ1.
          specialize (H1 A e2 k2).
          contradiction.

          destruct H1 as [A0 [e23 [k23 [B0 B1]]]].
          dependent destruction B0. 
          destruct (EE2 _ e23).
          inv H.
          inv B1.
        }  

 (*       - dependent destruction Heqot1; eauto with paco.  
     }        
*)

      { eapply IHruttF; eauto. pstep_reverse. 
        eapply eqit_inv_Tau_r; pstep; red; eauto.
      }  
  }

  
  (* 3: vis1 vis2 *)
  { remember (VisF e k2) as ot2.
    hinduction INR before CIH; intros; try discriminate.

    (* vis3 *)
    { dependent destruction Heqot2.
      constructor; eauto.

      intros a b H7.
      destruct (H0 _ _ H7), (REL a); try contradiction; eauto. 
    } 

    (* cut2 *)
    { dependent destruction Heqot2.
      eapply EqVisRet; eauto.
    }

    { dependent destruction Heqot2.
      pclearbot.
      eapply EqVisTau; eauto.
      red. right.
      eapply CIH; eauto.
      pstep; red.
      econstructor; eauto.
      intros.
      red. red. left. eauto.
    }
      
    { eapply EqTauR; eauto. }    
  }
      
  { eapply EqTauL; eauto. }

  { eapply IHINL; eauto.

    assert (rutt EE1 EE2 ER1 ER2 REv RAns RR (Tau t2) (go ot23)) as A. 
    { pstep; red; eauto. }

    eapply rutt_inv_Tau_l in A; eauto.
    punfold A; red in A.
  }
Qed.




Admitted.
  


        
        
        assert (ruttF EE1 EE2 ER1 ER2 REv RAns RR
            (upaco2 (rutt_ EE1 EE2 ER1 ER2 REv RAns RR) r) 
            (TauF m0) (VisF e2 k2)) as BB.
          
        { eapply EqTauVis; eauto.
          red.
          right.
          eapply CIH; eauto.
          instantiate (1:= m1).
           
          assert (m0 ≈ (Tau m1)) as A1.
          { pstep; red. auto. }
          
          eapply eqit_inv_Tau_r in A1; auto.
        
          pclearbot.
          punfold H0; red in H0.
          pstep; red. auto.
        }

(*        
      assert ((upaco2 (rutt_ EE1 EE2 ER1 ER2 REv RAns RR) bot2) <2=
                (upaco2 (rutt_ EE1 EE2 ER1 ER2 REv RAns RR) r)) as A1.
      { intros.
        red; red in PR.
        destruct PR; auto with *.
        left. 
        eapply paco2_mon_bot; eauto.
      }

      pclearbot. 
      
      eapply rutt_monot in A1.
      red in A1.
      assert (VisF e2 k2 = observe (Vis e2 k2)) as A0.
      { auto with paco. }
      rewrite A0.
      eexact A1.
      red.
      eauto with paco.
*)

        
(*        assert (rutt EE1 EE2 ER1 ER2 REv RAns RR (Tau m0) (Vis e2 k2)) as A1.
        { pstep; red; auto.  
*)        

        clear REL CIH H0.

        inversion BB; subst.
        dependent destruction H4.
        pclearbot.
        
        remember (TauF m0) as ot1.
        remember (VisF e2 k2) as ot2.
        hinduction BB before H; intros; try discriminate; eauto with paco.

        - dependent destruction Heqot1; eauto with paco.
          pclearbot.
          clear H2.
          red in H1.
          destruct H1.
          punfold H1; red in H1.

          admit.
          (*
          remember (observe m3) as ot3.
          destruct ot3.

          eapply EqRetVis; eauto.
          admit.

          eapply EqTauVis; eauto.
          red. right.
          *)
                     
        - dependent destruction Heqot1; eauto with paco.  
     }        

      { eapply IHruttF; eauto. pstep_reverse. 
        eapply eqit_inv_Tau_r; pstep; red; eauto.
      }  
  }

  
  (* 3: vis1 vis2 *)
  { remember (VisF e k2) as ot2.
    hinduction INR before CIH; intros; try discriminate.

    (* vis3 *)
    { dependent destruction Heqot2.
      constructor; eauto.

      intros a b H7.
      destruct (H0 _ _ H7), (REL a); try contradiction; eauto. 
    } 

    (* cut2 *)
    { dependent destruction Heqot2.
      eapply EqVisRet; eauto.
    }

    { dependent destruction Heqot2.
      pclearbot.
      eapply EqVisTau; eauto.
      red. right.
      eapply CIH; eauto.
      pstep; red.
      econstructor; eauto.
      intros.
      red. red. left. eauto.
    }
      
    { eapply EqTauR; eauto. }    
  }
      
  { eapply EqTauL; eauto. }

  { eapply IHINL; eauto.

    assert (rutt EE1 EE2 ER1 ER2 REv RAns RR (Tau t2) (go ot23)) as A. 
    { pstep; red; eauto. }

    eapply rutt_inv_Tau_l in A; eauto.
    punfold A; red in A.
  }
Admitted.
  
 

(*

     
        remember (TauF m1) as ot4.
        revert H0. revert Heqot4. revert m1.
        induction REL.

        5: {
        
        intros; try discriminate.

        3: {
          
        
        
        hinduction REL before CIH;
        intros; try discriminate.

        - dependent destruction Heqot4.
          eapply EqTauVis; eauto.
          red. right.
          pclearbot.
          eapply CIH; eauto.
        - pclearbot.
          eapply EqTauVis; eauto.
          red. right.
          eapply CIH; eauto.
          inv Heqot4.
          eapply eqit_inv_Tau_r.
          pstep; red. auto.

        - dependent destruction Heqot4.
          pclearbot.



          
          punfold H0; red in H0.
          remember (Vis e2 k2) as m4.

          hinduction H0 before IHREL.

          5: {
          ; intros; try discriminate.
          eapply IHREL; eauto.
                               

          (* PROBLEM *)
          admit.
      }

      

(****************)
      
      (* cut3 *)
      { clear EQ. pclearbot.
         

        
        remember (Vis e2 k2) as m4.
        revert REL.
        revert m0.
        clear t1 t1'.
        
        punfold H0; red in H0.
        hinduction H0 before CIH; intros; try discriminate. 

        

        assert (eqitF eq true true id (upaco2 (eqit_ eq true true id) bot2) 
                  (observe m0) (observe m1)) as REL1.
        { admit. }

        clear REL.

        remember (observe m0) as ot4.
        hinduction REL1 before CIH; intros; try discriminate.

        inv REL.
        eapply EqRetVis; eauto.
        
        
        
        remember (TauF m1) as ot4. (* remember m0 as ot3. *)

         

        
        hinduction REL before CIH; intros; try discriminate.

        3: { pclearbot.
             dependent destruction Heqot4.
             inv Heqot3.
             eapply IHREL; eauto.
        }

        pclearbot. eapply EqRetVis; eauto.
        admit.

        pclearbot.
        eapply EqTauVis; eauto.
        red. right.
        eapply CIH; eauto.
        
        - dependent destruction Heqot4.
          eapply EqTauVis; eauto.
          red. right.
          pclearbot.
          eapply CIH; eauto.
        - pclearbot.
          eapply EqTauVis; eauto.
          red. right.
          eapply CIH; eauto.
          inv Heqot4.
          eapply eqit_inv_Tau_r.
          pstep; red. auto.

        - dependent destruction Heqot4.
          pclearbot.

          (* PROBLEM *)
          admit.
      }


      
      
@eqitF_ind
     : forall (E : Type -> Type) (R1 R2 : Type) (RR : R1 -> R2 -> Prop)
         (b1 b2 : bool)
         (vclo : (itree E R1 -> itree E R2 -> Prop) ->
                 itree E R1 -> itree E R2 -> Prop)
         (sim : itree E R1 -> itree E R2 -> Prop)
         (P : itree' E R1 -> itree' E R2 -> Prop),
          
       (forall (r1 : R1) (r2 : R2), RR r1 r2 -> P (RetF r1) (RetF r2)) ->
          
       (forall (m1 : itree E R1) (m2 : itree E R2),
           sim m1 m2 -> P (TauF m1) (TauF m2)) ->
       
       (forall (u : Type) (e : E u) (k1 : u -> itree E R1)
          (k2 : u -> itree E R2),
           (forall v : u, vclo sim (k1 v) (k2 v)) ->
           P (VisF e k1) (VisF e k2)) ->
       
       (forall (t1 : itree E R1) (ot2 : itree' E R2),
        is_true b1 ->
        eqitF RR b1 b2 vclo sim (observe t1) ot2 ->
        P (observe t1) ot2 -> P (TauF t1) ot2) ->
       
       (forall (ot1 : itree' E R1) (t2 : itree E R2),
        is_true b2 ->
        eqitF RR b1 b2 vclo sim ot1 (observe t2) ->
        P ot1 (observe t2) -> P ot1 (TauF t2)) ->
       
       forall (i : itree' E R1) (i0 : itree' E R2),
         eqitF RR b1 b2 vclo sim i i0 -> P i i0




(**************)
      
      (* cut3 *)
      { clear EQ; remember (TauF m1) as ot4.
        hinduction REL before CIH; intros; try discriminate.

        - dependent destruction Heqot4.
          eapply EqTauVis; eauto.
          red. right.
          pclearbot.
          eapply CIH; eauto.
        - pclearbot.
          eapply EqTauVis; eauto.
          red. right.
          eapply CIH; eauto.
          inv Heqot4.
          eapply eqit_inv_Tau_r.
          pstep; red. auto.

        - dependent destruction Heqot4.
          pclearbot.

          (* PROBLEM *)
          admit.
      }
      
      { eapply IHruttF; eauto. pstep_reverse. 
        eapply eqit_inv_Tau_r; pstep; red; eauto.
      }  
  }




  
  (* 3: vis1 vis2 *)
  { remember (VisF e k2) as ot2.
    hinduction INR before CIH; intros; try discriminate.

    (* vis3 *)
    { dependent destruction Heqot2.
      constructor; eauto.

      intros a b H7.
      destruct (H0 _ _ H7), (REL a); try contradiction; eauto. 
    } 

    (* cut2 *)
    { dependent destruction Heqot2.
      eapply EqVisRet; eauto.
    }

    { dependent destruction Heqot2.
      pclearbot.
      eapply EqVisTau; eauto.
      red. right.
      eapply CIH; eauto.
      pstep; red.
      econstructor; eauto.
      intros.
      red. red. left. eauto.
    }
      
    { eapply EqTauR; eauto. }    
  }
      
  { eapply EqTauL; eauto. }

  { eapply IHINL; eauto.

    assert (rutt EE1 EE2 ER1 ER2 REv RAns RR (Tau t2) (go ot23)) as A. 
    { pstep; red; eauto. }

    eapply rutt_inv_Tau_l in A; eauto.
    punfold A; red in A.
  }
Abort.
  

*)

        
Lemma rutt_cong_eutt {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool) 
  (ER1 : forall X, E1 X -> R2 -> Prop)
  (ER2 : forall X, E2 X -> R1 -> Prop) :
  forall REv RAns RR
         (t1: itree E1 R1) t1' (t2: itree E2 R2),
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1 t2 ->
  t1 ≈ t1' ->
  rutt EE1 EE2 ER1 ER2 REv RAns RR t1' t2.
Proof.
  (* First by coinduction; then do an induction on Hrutt to expose the ruttF
     linking t1 and t2; then an induction on Heutt to expose the relation
     between t1 and t1'. Finally, explore ruttF until landing on an rutt where
     the t1/t1' relation can be substituted by CIH, and conclude. *)
  intros REv RAns RR t1 t1' t2 Hrutt Heutt.
  revert t1 t1' t2 Heutt Hrutt.
  ginit; gcofix CIH; intros t1 t1' t2 Heutt Hrutt.
  punfold Hrutt; red in Hrutt.
  
  rewrite (itree_eta t1) in Heutt.
  rewrite (itree_eta t2).

(*  assert (DEC: (exists t11, (observe t1') = TauF t11) \/
                 (forall t11, (observe t1') <> TauF t11)). *)

  assert (DEC: (forall (ot: itree' E1 R1), (exists t11, ot = TauF t11) \/
                 (forall t11, ot <> TauF t11))).
  { intro ot.
    destruct ot; eauto; right; red; intros; discriminate. }
  
  move Hrutt before CIH. move DEC before CIH. revert_until Hrutt.
  induction Hrutt as [ r1 r2 | m1 m2 | | | | | | m1 ot2 | ot1 m2 ];
   clear t1 t2; intros t1' Heutt.
  
  (* EqRet: t1 = Ret r1 ≈ t1'; we can rewrite away the Taus with the euttge
     closure and finish immediately with EqRet. *)
  { apply eutt_inv_Ret_l in Heutt. rewrite Heutt.
    gfinal; right; pstep. now apply EqRet.
  }  

  (* EqTau: The hardest case. When Heutt is EqTauL then we lack information to
     proceed, which requires that [desobs m1]. We then have to restart
     analyzing based on m1; the Ret case repeats EqRet above, while the Vis
     case repeats EqVis below. *)
  { punfold Heutt; red in Heutt; cbn in Heutt.
    rewrite itree_eta. pclearbot. 
    
(*    punfold H. red in H. eapply fold_ruttF in H. *)

    fold_ruttF H.
    remember (TauF m1) as ot1; revert m1 m2 H Heqot1.
    induction Heutt as [|m1_bis m1'| |m1_bis ot1' _|t1_bis m1'];
    intros * Hrutt Heqot1; clear t1'; try discriminate.
    + inv Heqot1. pclearbot. gfinal; right; pstep; red.
      apply EqTau. right. now apply (CIH m1).
    + inv Heqot1. rewrite (itree_eta m1) in Hrutt.      
      desobs m1 Hm1; clear m1 Hm1.
      { fold_eqitF Heutt. apply eutt_inv_Ret_l in Heutt.
        rewrite Heutt, tau_euttge.
        gfinal; right. eapply paco2_mon_bot; eauto. }
      { apply rutt_inv_Tau_l in Hrutt. eapply IHHeutt; eauto. }
      { clear IHHeutt. remember (VisF e k) as m1; revert Heqm1.
        induction Heutt as [| |U1 e1 k1 k1' Hk1k1'| |]; intros;
          try discriminate.        
        { symmetry in Heqm1; dependent destruction Heqm1.
          rewrite tau_euttge, (itree_eta m2).
          punfold Hrutt; red in Hrutt; cbn in Hrutt.
          remember (VisF e1 k1) as m1; revert Heqm1.
          induction Hrutt; intros; try discriminate.
          + dependent destruction Heqm1.
            gfinal; right. pstep; red; cbn.
            apply EqVis; auto. intros v1 v2 HAns. specialize (H0 v1 v2 HAns).
            hnf in H0; hnf. pclearbot; right. apply (CIH (k1 v1)); auto.
            apply Hk1k1'.
          + dependent destruction Heqm1.
            gstep. apply EqVisRet; auto.
          + dependent destruction Heqm1.
            pclearbot.
            gstep. apply EqVisTau; auto.
            gfinal. left. eapply CIH; eauto.
            pstep. red.
            econstructor; eauto.
            intros. unfold id. red. left; eauto.
        (*  * inv Heqm1.
            gstep. red. eapply EqVisTau; eauto. *)
          + idtac. rewrite tau_euttge, (itree_eta t2). now apply IHHrutt.
        }    
        { idtac. rewrite tau_euttge, itree_eta. now apply IHHeutt. }
      }
    + inv Heqot1. gfinal; right. pstep; red. apply EqTau. right.
      fold_eqitF Heutt. rewrite tau_euttge in Heutt. now apply (CIH m1).
  }
      
  (* EqVis: Similar to EqRet, but we don't have t1' ≳ Vis e1 k1 because the
     continuations are "only" ≈. The up-to-eutt principle that enforces Vis
     steps could work, but we don't have it for rutt. Instead we peel the Tau
     layers off t1' with a manual induction. *)
 (*  - rewrite itree_eta. gstep. red. simpl.   *) 
  { rewrite itree_eta. gfinal; right; pstep.
    rename H0 into HAns. punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e1 k1) as m1; revert Heqm1.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm1.
      apply EqVis; auto. intros a b HAns'. specialize (HAns a b HAns').      
      hnf in HAns; hnf. pclearbot; right. apply (CIH (k1 a)); auto. apply REL.
    + now apply EqTauL, IHHeutt.
  } 
      
  (* EqVisRet *)
  { rewrite itree_eta. gfinal; right; pstep.    
    remember (VisF e1 k1) as m1; revert Heqm1.
    punfold Heutt; red in Heutt; cbn in Heutt.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm1.
      apply EqVisRet; auto.
    + apply EqTauL. eapply IHHeutt; auto.   
  }
      
  (* EqRetVis *)
  { rewrite itree_eta. gfinal; right; pstep.
    remember (RetF r1) as m1; revert Heqm1.
    punfold Heutt; red in Heutt; cbn in Heutt.
    induction Heutt; intros; try discriminate.
    + dependent destruction Heqm1.
      apply EqRetVis; auto.
    + apply EqTauL. eapply IHHeutt; auto.   
  }
      
  (* EqVisTau *)
  { rewrite itree_eta. gfinal; right; pstep.
    
    punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e1 k1) as m1; revert Heqm1.
    induction Heutt; intros; try discriminate.

    dependent destruction Heqm1.

    + assert (eutt eq (Vis e1 k1) (Vis e1 k2)) as H1.
      { pstep. red. econstructor. auto. }

      red. econstructor; eauto.
      pclearbot; right. eapply CIH; eauto.
    + specialize (IHHeutt H0 Heqm1). 
      inv Heqm1.
      red. econstructor.
      right.

      assert (eutt eq (Vis e1 k1) t2) as H1.
      { pstep. red. auto. }

      pclearbot.
      eapply CIH; eauto.
  }

  (* EqTauL: We get a very strong IHHrutt at the ruttF level, which we can
     apply immediately; then handle the added Tau in ≈, which is trivial. *)
  2: { apply IHHrutt. rewrite <- itree_eta. now rewrite <- tau_eutt. }
    
  (* EqTauR: Adding a Tau on the side of t2 changes absolutely nothing to the
     way we rewrite t1, so we can follow down and recurse. *)
  2: { rewrite tau_euttge. rewrite (itree_eta m2). now apply IHHrutt. }
        
  (* EqTauVis.  idea: here we should have a coinductive call, so we
   need to use CIH. but in order to do that, we need to apply a
   constructor that give us a coinductive goal (and r goal). clearly,
   this should be EqTauVis. but this requires t1' = Tau t''. 
 *)
  - pclearbot.
    gstep; red.

    specialize (DEC (observe t1')).
    destruct DEC as [[t11 H1] | H1].
    { rewrite H1.

      assert (eutt eq m1 t11) as Heutt1.
      { rewrite (itree_eta t1') in Heutt.
        rewrite H1 in Heutt.
        eapply eqit_inv_Tau_l in Heutt.
        eapply eqit_inv_Tau_r in Heutt. eauto. }

      eapply EqTauVis; eauto. 
      gfinal. left.
        
      eapply CIH; eauto.
    }

    { punfold Heutt. red in Heutt.

      remember (observe (Tau m1)) as ot1.
      hinduction Heutt before CIH; intros.
      - inv Heqot1.
      - inv Heqot1.
        specialize (H1 m2). contradiction.
      - inv Heqot1.
      - inv Heqot1.
      - destruct ot2.
        + eapply EqRetVis; eauto.
          admit.
        + specialize (H1 t). contradiction.
        + eapply EqVis; eauto.
          admit.
          intros.
          gfinal. left.
          eapply CIH; eauto.   
          
      - specialize (H1 t2). contradiction.
        
  
        
      

    punfold Heutt; red in Heutt; cbn in Heutt.
    punfold Heutt1; red in Heutt1; cbn in Heutt1.
    
    remember (observe m1) as ot_m1.

    hinduction Heutt1 before CIH; intros; try discriminate.

    (* ret1 *)
    { eapply EqRetVis; eauto.
      inv REL.
      (* ok, from H0 with Heqot_m1 *)
      admit.
    }  

    (* tau1 *)
    { pclearbot.
      eapply EqTauVis; eauto.
      gfinal. left.
      eapply CIH; eauto.
      (* ok, from H0 with Heqot_m1 *)
      admit.
    }

    (* vis1 *)
    { econstructor; eauto.
      (* ok , rom H0 with Heqot_m1 *)
      admit.
      intros.
      (* ok , rom H0 with Heqot_m1 *)
      admit.
    }

    (* tau1 (again?) *)
    2: { eapply EqTauVis; eauto.
      gfinal. left.
      eapply (CIH m1 t2).
      (* ok *)
      admit.
      eauto.
    }  
    
    { (* tauL: NO GOOD. eapply IHHeutt1; eauto. *)

      (* PROBLEM : the inductive hypothesis does not work (requires a
 problematic hypothesis). on the other hand, coinduction cannot be
 applied, because there is no constructor we can apply to the goal
 (unless we destruct t1', but this leads to other problems).  *)
      
      specialize (IHHeutt1 _ e2 k2 m1).
      eapply IHHeutt1; eauto.
      (* PROBLEM *)
      admit.
    }
Abort.     





       
@ruttF_ind
     : forall (E1 E2 : Type -> Type) (R1 R2 : Type)
         (EE1 : forall X : Type, E1 X -> bool)
         (EE2 : forall X : Type, E2 X -> bool)
         (ER1 : forall X : Type, E1 X -> R2 -> Prop)
         (ER2 : forall X : Type, E2 X -> R1 -> Prop) 
         (REv : prerel E1 E2) (RAns : postrel E1 E2) 
         (RR : R1 -> R2 -> Prop) (sim : itree E1 R1 -> itree E2 R2 -> Prop)
         (P : itree' E1 R1 -> itree' E2 R2 -> Prop),
           
       (forall (r1 : R1) (r2 : R2), RR r1 r2 -> P (RetF r1) (RetF r2)) ->
           
       (forall (m1 : itree E1 R1) (m2 : itree E2 R2),
           sim m1 m2 -> P (TauF m1) (TauF m2)) ->
       
       (forall (A B : Type) (e1 : E1 A) (e2 : E2 B) 
          (k1 : A -> itree E1 R1) (k2 : B -> itree E2 R2),
        REv A B e1 e2 ->
        (forall (a : A) (b : B), RAns A B e1 a e2 b -> sim (k1 a) (k2 b)) ->
        P (VisF e1 k1) (VisF e2 k2)) ->
       
       (forall (A : Type) (e1 : E1 A) (k1 : A -> itree E1 R1) (r2 : R2),
           IsCut_ EE1 A e1 -> ER1 A e1 r2 -> P (VisF e1 k1) (RetF r2)) ->
       
       (forall (A : Type) (e2 : E2 A) (k2 : A -> itree E2 R2) (r1 : R1),
           IsCut_ EE2 A e2 -> ER2 A e2 r1 -> P (RetF r1) (VisF e2 k2)) ->
       
       (forall (A : Type) (e1 : E1 A) (k1 : A -> itree E1 R1)
          (m2 : itree E2 R2),
           IsCut_ EE1 A e1 -> sim (Vis e1 k1) m2 -> P (VisF e1 k1) (TauF m2)) ->
       
(***)  (forall (A : Type) (e2 : E2 A) (k2 : A -> itree E2 R2)
          (m1 : itree E1 R1),
           IsCut_ EE2 A e2 -> sim m1 (Vis e2 k2) -> P (TauF m1) (VisF e2 k2)) ->
       
       (forall (t1 : itree E1 R1) (ot2 : itree' E2 R2),
        ruttF EE1 EE2 ER1 ER2 REv RAns RR sim (observe t1) ot2 ->
        P (observe t1) ot2 -> P (TauF t1) ot2) ->
       
       (forall (ot1 : itree' E1 R1) (t2 : itree E2 R2),
        ruttF EE1 EE2 ER1 ER2 REv RAns RR sim ot1 (observe t2) ->
        P ot1 (observe t2) -> P ot1 (TauF t2)) ->
       
       forall (i : itree' E1 R1) (i0 : itree' E2 R2),
         
       ruttF EE1 EE2 ER1 ER2 REv RAns RR sim i i0 -> P i i0
 

(*    
    { (* NO GOOD: eapply IHHeutt1; eauto. *)

      punfold H0; red in H0. simpl in H0.
      remember (VisF e2 k2) as ot3.
      remember (observe m1) as ot4.
      hinduction H0 before CIH; intros; try discriminate.

      - inv Heqot_m1.
        dependent destruction Heqot3.
        eapply IHHeutt1; eauto.
        pstep; red.
        rewrite <- Heqot4.
        eapply EqTauVis; eauto.
        
        
        pstep; red.
        
     
      specialize (IHHeutt1 _ e2 k2 (Tau m1)).

      eapply IHHeutt1; eauto.
      pstep; red.
      punfold H0; red in H0.
      eapply EqTauL; eauto.

      econstructor; eauto.

      (* NO GOOD *)
      admit.
    }
*)

(*    
    { (* NO GOOD: eapply IHHeutt1; eauto. *)
      
      specialize (IHHeutt1 _ e2 k2 (Tau m1)).

      eapply IHHeutt1; eauto.
      pstep; red.
      punfold H0; red in H0.
      eapply EqTauL; eauto.

      econstructor; eauto.

      (* NO GOOD *)
      admit.
    }
*)

(*
      assert (eqit eq true true m1 (go ot2)) as A1.
      { admit. }

      
      
    { inv Heqot_m1.
      punfold H0; red in H0.
      eapply IHHeutt; eauto.
    
    
    remember (observe m1) as ot_m1. 
    remember (observe t1') as ot1.
    destruct ot1.

     
    
    gstep; red.
    rewrite <- Heqot1.
    eapply EqRetVis; eauto.
    hinduction Heutt before CIH; intros; try discriminate.
    inv REL.
    
    
    assert (exists ot_t1, eqitF eq false false id (eq_itree eq)
                        (observe t1') ot_t1) as A1.
    { exists (observe t1'). reflexivity. } 
    destruct A1 as [ot_t1 A1].
    
    

    
    eapply eqit_inv_Tau_l in Heutt.
    
 (*   specialize (CIH m1 t1' Heutt (Vis e2 k2) H0). *)

    punfold Heutt; red in Heutt; cbn in Heutt.

    remember (Vis e2 k2) as m2.
    remember (observe m1) as ot_m1. 
    (*  remember (observe t1') as ot_t1. *)
 

 
    destruct A1 as [ot_t1 A1].
    hinduction Heutt before CIH; intros; try discriminate.
    inv REL. 


    
    (*  dependent induction Heutt. *)
(*
    rewrite (itree_eta t1').
    rewrite <- Heqot_t1.
    gstep; red.
    eapply EqRetVis; auto.
    
    punfold H0. red in H0.
    rewrite <- Heqot_m1 in H0.
    dependent destruction H0; auto. 
*)  
    admit.
    
    admit.

    admit.

    admit.

    (** hard case *)
    
    eapply IHHeutt; eauto.
*)

 (* PROBLEM : the inductive hypothesis does not work (requires a
 problematic hypothesis). on the other hand, coinduction cannot be
 applied, because there is no constructor we can apply to the goal
 (unless we destruct t1', but this leads to other problems).  *)
    
    
(*    
    setoid_rewrite <- itree_eta in x.
    
    punfold Heutt; red in Heutt; cbn in Heutt.
    rewrite itree_eta. pclearbot.

(*    punfold H. red in H. eapply fold_ruttF in H. *)

    fold_ruttF H0.
    remember (Vis e2 k2) as m2. revert H0 Heqm2. revert m2.
    dependent induction Heutt; intros * Hrutt Heqot2; try discriminate.

    + inv x.
      gfinal; right; pstep; red.
      eapply EqTauVis; auto.
      pclearbot.
      right. eapply CIH; eauto.
    + inv Heqot2.
      gfinal; right; pstep; red.
      
    + 
      
    
    induction Heutt as [|m1_bis m1'| |m1_bis ot1' _|t1_bis m1'];
    intros * Hrutt Heqot2; try discriminate.

    inv REL.
    


    (* eapply eqit_inv_Tau_l in Heutt. *)

    rewrite itree_eta. gfinal; right; pstep.
    
    punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e2 k2) as m2; revert Heqm2.
    induction Heutt; intros; try discriminate.

    inv REL.
    red. eapply EqRetVis; auto.

    
    
    rewrite itree_eta. gfinal; right; pstep.
    red. simpl. pclearbot.

         
    punfold Heutt; red in Heutt; cbn in Heutt.
    rewrite itree_eta. pclearbot.

(*    punfold H. red in H. eapply fold_ruttF in H. *)

    fold_ruttF H0.
    remember (Vis e2 k2) as m2. revert H0 Heqm2. revert m2.
    induction Heutt as [|m1_bis m1'| |m1_bis ot1' _|t1_bis m1'];
    intros * Hrutt Heqot2; try discriminate.



    rewrite itree_eta. gfinal; right; pstep.
    
    punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e2 k2) as m2; revert Heqm2.
    induction Heutt. intros; try discriminate.

    dependent destruction Heqm2.

    + assert (eutt eq (Vis e1 k1) (Vis e1 k2)) as H1.
      { pstep. red. econstructor. auto. }

      red. econstructor; eauto.
      pclearbot; right. eapply CIH; eauto.
    + specialize (IHHeutt H0 Heqm1). 
      inv Heqm1.
      red. econstructor.
      right.

      assert (eutt eq (Vis e1 k1) t2) as H1.
      { pstep. red. auto. }

      pclearbot.
      eapply CIH; eauto.



   Heutt :
    eqitF eq true true id (upaco2 (eqit_ eq true true id) bot2) m1
      (observe t1')
*)
      
(**)
(*
    punfold Heutt; red in Heutt; cbn in Heutt.
    rewrite itree_eta. pclearbot.

(*    punfold H. red in H. eapply fold_ruttF in H. *)

    fold_ruttF H0.
    remember (TauF m2) as ot2. revert m2 ot2 H0 Heqot2.
    induction Heutt as [|m1_bis m1'| |m1_bis ot1' _|t1_bis m1'];
    intros * Hrutt Heqot2; try discriminate.
    + inv REL. gfinal. right.
      punfold Hrutt. red in Hrutt.
      pstep; red. apply EqTauR; eauto with paco. 
      assert ((upaco2 (rutt_ EE1 EE2 ER1 ER2 REv RAns RR) bot2) <2=
                (upaco2 (rutt_ EE1 EE2 ER1 ER2 REv RAns RR) r)) as A1.
      { intros.
        red; red in PR.
        destruct PR; auto with *.
        left. 
        eapply paco2_mon_bot; eauto.
      }
      eapply rutt_monot; eauto.
    + inv Heqot2.
      pclearbot. gfinal; right; pstep; red.
      apply EqTau. right.

      assert (paco2 (eqit_ eq true true id) bot2 (Tau m1_bis) m1') as H0.
      { pstep; red. punfold REL; red in REL. econstructor; eauto. }
      apply (CIH (Tau m1_bis) m1'); eauto.
    + 
*)
(*
      inv Heqot2. rewrite itree_eta. gfinal; right; pstep. red.
      eapply EqTauR.


      
    rename H0 into HAns. punfold Heutt; red in Heutt; cbn in Heutt.
    remember (VisF e1 k1) as m1; revert Heqm1.



      admit.
    + admit.  
    + admit.  
*)
(*      clear Hrutt.
      assert (ruttF EE1 EE2 ER1 ER2 REv RAns RR
    (upaco2 (rutt_ EE1 EE2 ER1 ER2 REv RAns RR) r) 
    (observe (Ret r2)) (observe m2) ->

        ruttF EE1 EE2 ER1 ER2 REv RAns RR
      (upaco2 (rutt_ EE1 EE2 ER1 ER2 REv RAns RR) bot2) 
      (observe (Ret r2)) (observe m2)).
      intros. eauto with paco.
*)

(*********************************************************************)

    
#[global] Instance rutt_Proper_R3 {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool) :
  Proper (eq_REv         (* REv *)
      ==> eq_RAns        (* RAns *)
      ==> @eq_rel R1 R2  (* RR *)
      ==> eutt eq        (* t1 *)
      ==> eutt eq        (* t2 *)
      ==> iff) (@rutt E1 E2 R1 R2 EE1 EE2).
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

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).

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
    intros. specialize (H2 a b H3). pclearbot. eauto 7 with paco.
  - gstep. econstructor; auto.
  - gstep. econstructor; auto.  
  - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
  - gclo. econstructor; auto_ctrans_eq; cycle -1; eauto; try reflexivity.
    eapply eqit_Tau_l. rewrite unfold_bind. reflexivity.
Qed.

End RuttBind.

Lemma rutt_bind {E1 E2 R1 R2}
      (EE1: forall X, E1 X -> bool)
      (EE2: forall X, E2 X -> bool)
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

Definition EE_MR {E: Type -> Type}
  (EE: forall X, E X -> bool) (D: Type -> Type) :
  forall X, (D +' E) X -> bool :=
  fun X m => match m with
             | inl1 _ => true
             | inr1 e => EE X e end.             

Section RuttMrec.
  Context {D1 D2 E1 E2 : Type -> Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).
            
  Context (RPre : prerel E1 E2) (RPreInv : prerel D1 D2)
          (RPost : postrel E1 E2) (RPostInv : postrel D1 D2).

  Context (bodies1 : D1 ~> itree (D1 +' E1))
          (bodies2 : D2 ~> itree (D2 +' E2)).
  
  Context (Hbodies : forall R1 R2 (d1 : D1 R1) (d2 : D2 R2), 
              RPreInv R1 R2 d1 d2 -> 
              @rutt (D1 +' E1) (D2 +' E2)
                R1 R2
                (EE_MR EE1 D1)
                (EE_MR EE2 D2)               
                (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
                (fun (v1 : R1) (v2 : R2) =>
                   RPostInv R1 R2 d1 v1 d2 v2)
                     (bodies1 R1 d1) (bodies2 R2 d2) ).

  Lemma interp_mrec_rutt (R1 R2 : Type) (RR : R1 -> R2 -> Prop) :
    forall (t1 : itree (D1 +' E1) R1) (t2 : itree (D2 +' E2) R2),
      rutt (EE_MR EE1 D1) (EE_MR EE2 D2)
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
      destruct H1.
      + gstep. constructor.
        gfinal. left. eapply CIH; eauto.
        eapply rutt_bind; eauto.
        intros. cbn in H1. clear - H1 H2.
        specialize (H2 r1 r2 (sum_postrel_inl _ _ _ _ _ _ _ _ H1)).
        pclearbot. auto.
      + gstep. red. constructor; eauto.
        intros. 
        gstep. constructor.
        gfinal. left. eapply CIH.
        specialize (H2 a b (sum_postrel_inr _ _ _ _ _ _ _ _ H1)).
        pclearbot. eauto.
    - apply simpobs in Heqot1.
      rewrite Heqot1. 
      rewrite unfold_interp_mrec at 1. 
      cbn.
      destruct e1; simpl in H; try congruence.
      gstep. red.
      econstructor; auto.        
    - apply simpobs in Heqot2.
      rewrite Heqot2. 
      setoid_rewrite unfold_interp_mrec at 2. 
      cbn.
      destruct e2; simpl in H; try congruence.
      gstep. red.
      econstructor; auto.        
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

Section RuttRec.
  Context (E1 E2 : Type -> Type) {A1 A2 B1 B2: Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).
            
  Context (bodies1 : A1 -> itree (callE A1 B1 +' E1) B1)
          (bodies2 : A2 -> itree (callE A2 B2 +' E2) B2).
  
  Context (RPre : prerel E1 E2) (RPreInv : prerel (callE A1 B1) (callE A2 B2))
     (RPost : postrel E1 E2) (RPostInv : postrel (callE A1 B1) (callE A2 B2)).

  Context (Hbodies: forall (A B : Type)
                           (d1 : callE A1 B1 A) (d2 : callE A2 B2 B),
  RPreInv A B d1 d2 -> 
  rutt (EE_MR EE1 (callE A1 B1)) (EE_MR EE2 (callE A2 B2))  
    (sum_prerel RPreInv RPre) (sum_postrel RPostInv RPost)
    (fun (a : A) (b : B) => RPostInv A B d1 a d2 b) 
    (calling' bodies1 A d1) (calling' bodies2 B d2)).

  Lemma rec_rutt a1 a2 : 
    RPreInv B1 B2 (Call a1) (Call a2) -> 
    rutt EE1 EE2 RPre RPost
      (fun (t1 : B1) (t2 : B2) =>  
         RPostInv B1 B2 (Call a1) t1 (Call a2) t2) 
         (rec bodies1 a1) (rec bodies2 a2).
  Proof.
    unfold rec.
    eapply mrec_rutt with (RPreInv:=RPreInv). eauto.
  Qed.  
  
End RuttRec.

(** Relating [X-rutt] and [iter] *)

Section RuttIter.
  Context {E1 E2 : Type -> Type}.

  Context (EE1: forall X, E1 X -> bool).
  Context (EE2: forall X, E2 X -> bool).

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
    @rutt E1 E2 R1 R2 EE1 EE2 RPreE RPostE RR
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

