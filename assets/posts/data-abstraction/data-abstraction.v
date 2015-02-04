Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Basics.
Require Import Arith.
Require Import Omega.
Require Import FunctionalExtensionality.

(** Utility Functions **)
Module Utils.

  Definition natEqDec (a b:nat) : {a = b} + {a <> b}.
    decide equality.
  Defined.
  Notation "a =? a'" := (natEqDec a a').
  Notation "a <=? b" := (leb a b).

  Fixpoint contains (l:list nat) a :=
    match l with
    | h :: t => if h =? a then true else contains t a
    | [] => false
    end.

  Definition isEmpty (l:list nat) :=
    match l with
    | [] => true
    | h :: t => false
    end.

  Inductive Tree :=
  | node : nat -> Tree -> Tree -> Tree
  | leaf : Tree.

  Fixpoint search n (t:Tree) : bool :=
    match t with
    | node m l r => if n =? m then       
                      true
                    else if n <=? m then 
                      search n l
                    else
                      search n r
    | leaf => false
    end.
End Utils.
Import Utils.

(** ADTs **)
Definition id A (a:A) := a.

Definition min A (le:A->A->bool) (a b:A) :=
  if le a b then a else b.

Definition ADT := sigT.

Module IntSet.
  Record IntSet := { 
    A : Type; 
    contains : A -> nat -> bool;
    empty : A;
    emptyOk : forall n, contains empty n = false;
    union : A -> A -> A;
    unionOk : forall n a b, contains (union a b) n = 
                            contains a n && contains b n
  }.
End IntSet.

Module Monoid.
  Record Monoid := {
    A : Type;
    add : A -> A -> A;
    one : A;
    _ : forall a, add a one = a;
    _ : forall a, add one a = a;
    _ : forall a b c, add (add a b) c = add a (add b c)
  }.
End Monoid.

Module Order.
  Record Order := {
    A : Type;
    le : A -> A -> bool
    (* eliding antisymmetry, transitivity, totality *)
  }.

  Definition min (o:Order) (a b : A o) : A o :=
    if le o a b then a else b.

  Definition natOrder := {|A:=nat; le:=leb|}.

  Compute (min natOrder 9 3).
End Order.

Module OrderClass.
  Class Order := {
    A : Type;
    le : A -> A -> bool
  }.

  Definition min `{Order} (a b : A) : A :=
    if le a b then a else b.

  Instance natOrder : Order := {|A:=nat; le:=leb|}.

  Compute (min 9 3).
End OrderClass.


(** OOP **)
Module SimpleOOP.
  Definition contains (n:nat) (s:nat -> bool) := s n.
End SimpleOOP.

Module OOP.
  Definition IntSet := nat -> bool.

  Definition emptySet : IntSet := fun _ => false.

  Definition evenSet : IntSet :=
    fix R n := match n with 
    | 0 => true
    | 1 => false
    | S (S n) => R n
    end.

  Definition listSet (l:list nat) : IntSet := fun n => contains l n.

  Definition treeSet (t:Tree) : IntSet := fun n => search n t.

  Definition someListSet : IntSet := listSet [1;3;4;6;9;11].

  Definition someTreeSet : IntSet := treeSet
    (node 6 
      (node 3 
        (node 1 leaf leaf)
        (node 4 leaf leaf))
      (node 9 leaf
        (node 11 leaf leaf))).

  Goal someListSet = someTreeSet. 
    apply functional_extensionality.
    intro n.
    do 12 (destruct n; auto).
  Qed. 
  
  Inductive PairMethod := fst | snd.

  Definition BoolNatPair : Type := forall m:PairMethod, 
    match m with fst => bool | snd => nat end.

  Definition makePair a b : BoolNatPair := fun m => match m with
    | fst => a
    | snd => b
    end.

  Compute (makePair true 8) fst.
  Compute (makePair true 8) snd.

  Definition union (s:IntSet) (t:IntSet) : IntSet :=
    fun n => s n || t n.
End OOP.

Module OOPProblems.
  Inductive IntSetMethod := contains | isEmpty | isEmptyOk | empty | union.

  Definition IntSet : Type.
  (*refine (forall m:IntSetMethod, match m with
    circumvent refine bug *)
    pose (fun f => forall a:IntSetMethod, f a) as H; apply H; clear H; intro m.
    refine (match m with
    | contains => nat -> bool
    | isEmpty  => bool
    | isEmptyOk => _
    | empty => _
    | union => _
    end).
    - (* Cannot refer to object: forall n, this contains n = false *) admit.
    - (* Cannot refer to type:   IntSet *) admit.
    - (* Cannot refer to type:   IntSet *) admit.
  Abort. 
End OOPProblems.
