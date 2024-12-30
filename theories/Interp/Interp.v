(** * Monadic interpretations of interaction trees *)

(** We can derive semantics for an interaction tree [itree E ~> M]
    from semantics given for every individual event [E ~> M],
    when [M] is a monad (actually, with some more structure).

    We define the following terminology for this library.
    Other sources may have different usages for the same or related
    words.

    The notation [E ~> F] stands for [forall T, E T -> F T]
    (in [ITree.Basics]).
    It can mean many things, including the following:

    - The semantics of itrees are given as monad morphisms
      [itree E ~> M], also called "interpreters".

    - "ITree interpreters" (or "itree morphisms") are monad morphisms
      where the codomain is made of ITrees: [itree E ~> itree F].

    Interpreters can be obtained from handlers:

    - In general, "event handlers" are functions [E ~> M] where
      [M] is a monad.

    - "ITree event handlers" are functions [E ~> itree F].

    Categorically, this boils down to saying that [itree] is a free
    monad (not quite, but close enough).
 *)

(* begin hide *)
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Core.ITreeDefinition
     Indexed.Relation
     Indexed.Sum.
(* end hide *)

(** ** Translate *)

(** An event morphism [E ~> F] lifts to an itree morphism [itree E ~> itree F]
    by applying the event morphism to every visible event.  We call this
    process _event translation_.

    Translation is a special case of interpretation:
[[
    translate h t ≈ interp (trigger ∘ h) t
]]
    However this definition of [translate] yields strong bisimulations
    more often than [interp].
    For example, [translate (id_ E) t ≅ id_ (itree E)].
*)

(** A plain event morphism [E ~> F] defines an itree morphism
    [itree E ~> itree F]. *)
Definition translateF {Er Ef Fr Ff T R}
 (h : (tau T +' Er +' Ef) ~> (tau T +' Fr +' Ff))
 (rec: itree Er Ef T R -> itree Fr Ff T R)
 (t : itreeF Er Ef T R _) : itree Fr Ff T R  :=
  match t with
  | RetF x => Ret x
  | VisF e k => Vis (h _ e) (fun x => rec (k x))
  end.

Definition translate {Er Ef Fr Ff T}
  (h : (tau T +' Er +' Ef) ~> (tau T +' Fr +' Ff))                     
  : itree Er Ef T ~> itree Fr Ff T
  := fun R => cofix translate_ t := translateF h translate_ (observe t).

Arguments translate {Er Ef Fr Ff T} & h [T0].

(** ** Interpret *)

(** An event handler [E ~> M] defines a monad morphism
    [itree E ~> M] for any monad [M] with a loop operator. *)

Definition interp {Er Ef M : Type -> Type} {T}
           {FM : Functor M} {MM : Monad M} {IM : MonadIter M}
           (h : (tau T +' Er +' Ef) ~> M) :
  itree Er Ef T ~> M := fun R =>
  iter (fun t =>
    match observe t with
    | RetF r => ret (inr r)
    | VisF e k => fmap (fun x => inl (k x)) (h _ e)
    end).
(* TODO: this does a map, and aloop does a bind. We could fuse those
   by giving aloop a continuation to compose its bind with.
   (coyoneda...) *)

Arguments interp {Er Ef M T FM MM IM} & h [T0].
