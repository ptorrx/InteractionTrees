(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITreeDefinition
     Indexed.Sum.

Import ITreeNotations.
#[local] Open Scope itree_scope.
(* end hide *)

(** * General recursion *)

(** *** Mutual recursion *)

(* Implementation of the fixpoint combinator over interaction
 * trees.
 *
 * The implementation is based on the discussion here
 *   https://gmalecha.github.io/reflections/2018/compositional-coinductive-recursion-in-coq
 *)

(* The indexed type [D : Type -> Type] gives the signature of
   a set of functions. For example, a pair of mutually recursive
   [even : nat -> bool] and [odd : nat -> bool] can be declared
   as follows:

[[
   Inductive D : Type -> Type :=
   | Even : nat -> D bool
   | Odd  : nat -> D bool.
]]

   Their mutually recursive definition can then be written finitely
   (without [Fixpoint]):

[[
   Definition def : D ~> itree (D +' void1) := fun _ d =>
     match d with
     | Even n => match n with
                 | O => ret true
                 | S m => trigger (Odd m)
                 end
     | Odd n => match n with
                | O => ret false
                | S m => trigger (Even m)
                end
     end.
]]

   The function [interp_mrec] below then ties the knot.

[[
   Definition f : D ~> itree void1 :=
     interp_mrec def.

   Definition even (n : nat) : itree void1 bool := f _ (Even n).
   Definition odd  (n : nat) : itree void1 bool := f _ (Odd n).
]]

   The result is still in the [itree] monad of possibly divergent
   computations, because [mutfix_itree] doesn't care whether
   the mutually recursive definition is well-founded.

 *)

(** Interpret an itree in the context of a mutually recursive
    definition ([ctx]). *)

(* CHECK THE TYPES *)

Definition interp_mrec {Df Er Ef : Type -> Type} {T}
  (ctx : Df ~> itree Er (Df +' Ef) T) :
  itree Er (Df +' Ef) T ~> itree Er Ef T :=
  fun R =>
    ITree.iter (fun t : itree Er (Df +' Ef) T R =>
      match observe t with
      | RetF r => Ret (inr r)
      | @VisF _ _ _ _ _ X0 (inl1 t) k =>
          Ret (inl (@tauF_interp _ _ _ _ _ _ _ (VisF (inl1 t) k) eq_refl))             
      | @VisF _ _ _ _ _ X0 (inr1 (inl1 er)) k => 
          Vis (inr1 (inl1 er)) (fun x => Ret (inl (k x)))
      | @VisF _ _ _ _ _ X0 (inr1 (inr1 (inl1 df))) k =>
          Ret (inl (ctx _ df >>= k))
      | @VisF _ _ _ _ _ X0 (inr1 (inr1 (inr1 ef))) k =>
          Vis (inr1 (inr1 ef)) (fun x => Ret (inl (k x)))
      end).    

Arguments interp_mrec {Df Er Ef T} & ctx [T0].

(** Unfold a mutually recursive definition into separate trees,
    resolving the mutual references. *)
Definition mrec {Df Er Ef : Type -> Type} {T}
           (ctx : Df ~> itree Er (Df +' Ef) T) : Df ~> itree Er Ef T :=
  fun R d => interp_mrec ctx (ctx _ d).

Arguments mrec {Df Er Ef T} & ctx [T0].

(** Make a recursive call in the handler argument of [mrec]. *)
Definition trigger_inl1 {Df Er Ef : Type -> Type} {T} :
  Df ~> itree Er (Df +' Ef) T
  := fun _ d => ITree.trigger (inr1 (inl1 d)).

Arguments trigger_inl1 {Df Er Ef} {T} [T0].

(** Here's some syntactic sugar with a notation [mrec-fix]. *)

(** Short for endofunctions, used in [mrec_fix] and [rec_fix]. *)
Local Notation endo T := (T -> T).

Definition mrec_fix {Df Er Ef : Type -> Type} {T}
           (ctx : endo (Df ~> itree Er (Df +' Ef) T))
  : Df ~> itree Er Ef T
  := mrec (ctx trigger_inl1).

Arguments mrec_fix {Df Er Ef} {T} &.

Notation "'mrec-fix' f d := g" :=
	(let Df := _ in
	 mrec_fix (Df := Df)
           (fun (f : forall T, Df T -> _) T0 (d : Df T0) => g))
  (at level 200, f name, d pattern).
(* No idea what a good level would be. *)

(** *** Simple recursion *)

Inductive callE (A B : Type) : Type -> Type :=
| Call : A -> callE A B B.

Arguments Call {A B}.

(** Get the [A] contained in a [callE A B]. *)
Definition unCall {A B T} (e : callE A B T) : A :=
  match e with
  | Call a => a
  end.

(** Lift a function on [A] to a morphism on [callE]. *)
Definition calling {A B} {F : Type -> Type}
           (f : A -> F B) : callE A B ~> F :=
  fun _ e =>
    match e with
    | Call a => f a
    end.

(* TODO: This is identical to [callWith] but [rec] finds a universe
   inconsistency with [calling], and not with [calling'].
   The inconsistency now pops up later (currently in [Events.Env]) *)
Definition calling' {A B} {Fr Ff : Type -> Type} {T}
           (f : A -> itree Fr Ff T B) : callE A B ~> itree Fr Ff T :=
  fun _ e =>
    match e with
    | Call a => f a
    end.

(* Interpret a single recursive definition. *)
Definition rec {Er Ef : Type -> Type} {T} {A B : Type}
           (body : A -> itree Er (callE A B +' Ef) T B) :
  A -> itree Er Ef T B :=
  fun a => mrec (calling' body) (Call a).

Arguments rec {Er Ef T A B} &.

(** An easy way to construct an event suitable for use with [rec].
    [call] is an event representing the recursive call.  Since in general, the
    function might have other events of type [E], the resulting itree has
    type [(callE A B +' E)].
*)
Definition call {Er Ef T A B} (a:A) :
  itree Er (callE A B +' Ef) T B := ITree.trigger (inr1 (inl1 (Call a))).

(** Here's some syntactic sugar with a notation [mrec-fix]. *)

Definition rec_fix {Er Ef : Type -> Type} {T} {A B : Type}
           (body : endo (A -> itree Er (callE A B +' Ef) T B))
  : A -> itree Er Ef T B
  := rec (body call).

Arguments rec_fix {Er Ef T A B} &.

Notation "'rec-fix' f a := g" := (rec_fix (fun f a => g))
  (at level 200, f name, a pattern).
(* No idea what a good level would be. *)
