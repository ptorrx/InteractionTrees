(** * Shallow equivalence *)

(** Equality under [observe]:

[[
  observing eq t1 t2 <-> t1.(observe) = t2.(observe)
]]

  We actually define a more general relation transformer
  [observing] to lift arbitrary relations through [observe].
 *)

(* begin hide *)
From Coq Require Import Morphisms.

From ITree Require Import Core.ITreeDefinition
                          Indexed.Sum. 

Set Implicit Arguments.
(* end hide *)

Definition eqeq {A : Type} (P : A -> Type) {a1 a2 : A} (p : a1 = a2) : P a1 -> P a2 -> Prop :=
  match p with
  | eq_refl => eq
  end.

Definition pweqeq {R1 R2} (RR : R1 -> R2 -> Prop) {X1 X2 : Type} (p : X1 = X2)
  : (X1 -> R1) -> (X2 -> R2) -> Prop :=
  match p with
  | eq_refl => fun k1 k2 => forall x, RR (k1 x) (k2 x)
  end.

Lemma pweqeq_mon {R1 R2} (RR1 RR2 : R1 -> R2 -> Prop) X1 X2 (p : X1 = X2) k1 k2
  : (forall r1 r2, RR1 r1 r2 -> RR2 r1 r2) -> pweqeq RR1 p k1 k2 -> pweqeq RR2 p k1 k2.
Proof.
  destruct p; cbn; auto.
Qed.

Lemma eq_inv_VisF_weak {Er Ef T R X1 X2}
  (e1 : (tau T +' Er +' Ef) X1)
  (e2 : (tau T +' Er +' Ef) X2)
  (k1 : X1 -> itree Er Ef T R)
  (k2 : X2 -> itree Er Ef T R)
  : VisF (R := R) e1 k1 = VisF (R := R) e2 k2 ->
    exists p : X1 = X2, eqeq (tau T +' Er +' Ef) p e1 e2 /\
       eqeq (fun X => X -> itree Er Ef T R) p k1 k2.
Proof.
  refine (fun H =>
    match H in _ = t return
      match t with
      | VisF e2 k2 => _
      | _ => True
      end
    with
    | eq_refl => _
    end); cbn.
  exists eq_refl; cbn; auto.
Qed.

Ltac inv_Vis :=
  discriminate +
  match goal with
  | [ E : VisF _ _ = VisF _ _ |- _ ] =>
     apply eq_inv_VisF_weak in E; destruct E as [ <- [<- <-]]
  end.

(** ** [observing]: Lift relations through [observe]. *)
Record observing {Er Ef T R1 R2}
           (eq_ : itree' Er Ef T R1 -> itree' Er Ef T R2 -> Prop)
           (t1 : itree Er Ef T R1) (t2 : itree Er Ef T R2) : Prop :=
  observing_intros
  { observing_observe : eq_ (observe t1) (observe t2) }.
#[global] Hint Constructors observing : itree.

Section observing_relations.

Context {Er Ef : Type -> Type} {T R : Type}.
Variable (eq_ : itree' Er Ef T R -> itree' Er Ef T R -> Prop).

#[global]
Instance observing_observe_ :
  Proper (observing eq_ ==> eq_) (@observe Er Ef T R).
Proof. intros ? ? []; cbv; auto. Qed.

#[global]
Instance observing_go : Proper (eq_ ==> observing eq_) (@go Er Ef T R).
Proof. cbv; auto with itree. Qed.

#[global]
Instance monotonic_observing eq_' :
  subrelation eq_ eq_' ->
  subrelation (observing eq_) (observing eq_').
Proof. intros ? ? ? []; cbv; eauto with itree. Qed.

#[global]
Instance Equivalence_observing :
  Equivalence eq_ -> Equivalence (observing eq_).
Proof with (auto with itree).
  intros []; split; cbv...
  - intros ? ? []; auto...
  - intros ? ? ? [] []; eauto with itree.
Qed.

End observing_relations.

(** ** Unfolding lemmas for [bind] *)

Lemma observe_bind {Er Ef : Type -> Type} {T R S : Type}
  (t : itree Er Ef T R) (k : R -> itree Er Ef T S)
  : observe (ITree.bind t k)
  = observe (match observe t with
    | RetF r => k r
    | @VisF _ _ _ _ _ X e ke => Vis e (fun x : X => ITree.bind (ke x) k)
    end).
Proof. reflexivity. Qed.

#[global]
Instance observing_bind {Er Ef T R S} :
  Proper (observing eq ==> eq ==> observing eq) (@ITree.bind Er Ef T R S).
Proof.
  repeat intro; subst. constructor. unfold observe. cbn.
  rewrite (observing_observe H). reflexivity.
Qed.

Lemma bind_ret_ {Er Ef T R S} (r : R) (k : R -> itree Er Ef T S) :
  observing eq (ITree.bind (Ret r) k) (k r).
Proof. constructor; reflexivity. Qed.

Lemma bind_tau_ {Er Ef T R} U t (k: U -> itree Er Ef T R) :
  observing eq (ITree.bind (Tau t) k) (Tau (ITree.bind t k)).
Proof. constructor; reflexivity. Qed.

Lemma bind_vis_ {Er Ef T R U V}
  (e: (tau T +' Er +' Ef) V)
  (ek: V -> itree Er Ef T U) (k: U -> itree Er Ef T R) :
  observing eq
    (ITree.bind (Vis e ek) k)
    (Vis e (fun x => ITree.bind (ek x) k)).
Proof. constructor; reflexivity. Qed.

(** Unfolding lemma for [aloop]. There is also a variant [unfold_aloop]
    without [Tau]. *)
Lemma unfold_aloop_ {Er Ef T A B} (f : A -> itree Er Ef T (A + B)) (x : A) :
  observing eq
    (ITree.iter f x)
    (ITree.bind (f x) (fun lr => ITree.on_left lr l (Tau (ITree.iter f l)))).
Proof. constructor; reflexivity. Qed.

(** Unfolding lemma for [forever]. *)
Lemma unfold_forever_ {Er Ef T R S} (t: itree Er Ef T R):
  observing eq (@ITree.forever Er Ef T R S t)
    (ITree.bind t (fun _ => Tau (ITree.forever t))).
Proof. econstructor. reflexivity. Qed.

(** ** [going]: Lift relations through [go]. *)

Inductive going {Er Ef T R1 R2}
  (r : itree Er Ef T R1 -> itree Er Ef T R2 -> Prop)
  (ot1 : itree' Er Ef T R1) (ot2 : itree' Er Ef T R2) : Prop :=
| going_intros : r (go ot1) (go ot2) -> going r ot1 ot2.
#[global] Hint Constructors going : itree.

Lemma observing_going {Er Ef T R1 R2}
  (eq_ : itree' Er Ef T R1 -> itree' Er Ef T R2 -> Prop) ot1 ot2 :
  going (observing eq_) ot1 ot2 <-> eq_ ot1 ot2.
Proof.
  split; auto with itree.
  intros [[]]; auto.
Qed.

Section going_relations.

Context {Er Ef : Type -> Type} {T R : Type}.
Variable (eq_ : itree Er Ef T R -> itree Er Ef T R -> Prop).

#[global]
Instance going_go : Proper (going eq_ ==> eq_) (@go Er Ef T R).
Proof. intros ? ? []; auto. Qed.

#[global]
Instance monotonic_going eq_' :
  subrelation eq_ eq_' ->
  subrelation (going eq_) (going eq_').
Proof. intros ? ? ? []; eauto with itree. Qed.

#[global]
Instance Equivalence_going :
  Equivalence eq_ -> Equivalence (going eq_).
Proof.
  intros []; constructor; cbv; eauto with itree.
  - intros ? ? []; auto with itree.
  - intros ? ? ? [] []; eauto with itree.
Qed.

End going_relations.
