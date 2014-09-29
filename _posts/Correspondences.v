Require Import Arith.

Section Sugar.
(*** Desugaring Coq ***)

(** 
Coq comes with a lot of concepts. We attempt to find a small subset of
concepts that is sufficient to define all other concepts.

The original CoC paper [0] only contains forall and fun. Can we build
all other concepts out of these?

Church Encoding suggests a way to do exactly that. System F's type
system is powerful enough to type some church encondings [1].

Let us now define some finite types. This heavily depends on
parametricity.  Note that the church encoding of a type is similar to
its recursor.

[0] Th. Coquand and G. Huet. The Calculus of Constructions. 
[1] http://en.wikipedia.org/wiki/System_F
**)

Check Empty_set_rect.
(*
  Empty_set_rect : forall (P : Empty_set -> Type) (e : Empty_set), P e
*)

(**
We see that the church encoding is just the recurser for 
non-dependent P.
  
  Empty_set_rect_nd : forall (T:Type), T

**)

Definition Empty_set' := forall T:Type, T.

(**
Let us now define unit and bool.
**)

Check unit_rect.
Definition unit' := forall T:Type, T -> T.
Definition tt' : unit' := fun _ t => t.

(**
We apparently do not necessarily require functional extensionality.
**)
Definition tt''  : unit' := fun _ t => (fun t' => t') t.
Definition tt''' : unit' := fun _ t => match cons t nil with nil=>t | cons t' _ => t' end.

Goal tt' = tt'' /\ tt'=tt'''.
  compute.
  auto.
Qed.

Check bool_rect.
Definition bool' := forall T:Type, T -> T -> T.
Definition true'  : bool' := fun _ t _  => t.
Definition false' : bool' := fun _ _ t' => t'.

(** 
Non-dependent matches work just fine ...
**)

Notation "'whenever' b 'choose' x 'otherwise' y" := (b _ x y) (at level 40).

Compute let b : bool' := false' in 
  whenever b choose 4 otherwise 7.

(** 
But when we define depedent pairs, and require dependent matches,
things break down ...
**)

Check sigT_rect.
Definition sigT' (A:Type) (B:A->Type) := (forall T, (forall a:A, B a -> T) -> T).
Definition existT' A B a b : sigT' A B := fun _ f => f a b.

Goal nat. 
  refine (let p := existT' _ (fun b:bool' => whenever b choose nat otherwise unit) true' 7 in _).
  refine (p nat (fun b v => _)).
  refine (b nat _ 4).
  (** we do not know that the bool' was true', and thus that v is a
     nat. **)
Abort.

(**
We cannot proof (and thus define) the dependent recurser in CoC
directly [2].  For this reason, inductive types were introduced. The
question arrises --- do we need full blown induction, or is it enough
to have a small number of built in inductive types that are powerful
enough to build all the others?

Aaron Stump talks about this [3][4][5].

[2] Pfenning and Paulin-Mohring, Inductively Defined Types in the
Calculus of Constructions 
[3] http://queuea9.wordpress.com/2012/03/28/why-not-lambda-encode-data/
[4] Dependently-Typed Programming with Scott Encoding
[5] Dependently-Typed Programming with Church Encoding
**)

(**
Inductively defined dependent products can be used to replace normal products.
**)

Print prod.
Print sigT.
(*
  Inductive prod (A : Type) (B : Type)      : Type := pair   : A          -> B   -> A * B
  Inductive sigT (A : Type) (P : A -> Type) : Type := existT : forall x : A, P x -> sigT P
*)

Definition prod' (A B:Type) := {_:A & B}.
Definition pair' {A B:Type} (a:A) (b:B) : prod' A B := (existT _ a b).

Check prod_rect.
Definition prod_rect' A B (P:prod' A B -> Type) 
                      (f:forall a b, P (pair' a b)) 
                      p : P p := 
  match p with
  | existT a b => f a b
  end.

(**
There is no dependent sum, because left/right cannot depend the value
of the other.  Yet, dependent products can be used to replace normal
sums, given inductively defined booleans.
**)

Print sum.
(*
  Inductive sum (A B : Type) : Type :=  inl : A -> A + B | inr : B -> A + B
*)

Definition sum' (A B:Type) := {b:bool & if b then A else B}.
Definition inl' {A:Type} (B:Type) (a:A) : sum' A B := (existT (fun b:bool => if b then A else B) true  a).
Definition inr' (A:Type) {B:Type} (b:B) : sum' A B := (existT (fun b:bool => if b then A else B) false b).

Check sum_rect.
Definition sum_rect' A B (P : sum' A B -> Type) 
                     (l:forall a : A, P (inl' _ a))
                     (r:forall b : B, P (inr' _ b)) 
                     s : P s.
  refine (
    match s with
    | existT b v => _
    end).
  refine (
    match b as b' return 
      forall v':(if b' return Type then A else B),
      P (existT (fun b:bool=>if b then A else B) b' v')
    with
    | true  => l
    | false => fun v' => _ 
    end v).
  exact (r v').
Defined.

(**
Inductive types are closely related to products and sums.  Consider
the following inductive type:
**)

Inductive Router (IP:Type) :=
| external : IP -> Router IP
| internal : IP -> list IP -> Router IP.

(**
We can build the same type using only sums and products.
**)

Definition Router' (IP:Type) := sum' IP (prod' IP (list IP)).
Definition external' IP ip : Router' IP := inl' _ ip.
Definition internal' IP ip neighbors : Router' IP := inr' _ (pair' ip neighbors).

Check Router_rect.
Definition Router_rect' IP (P : Router' IP -> Type)
                        (e:forall i:IP, P (external' IP i))
                        (i:forall (i:IP) (l:list IP), P (internal' IP i l))
                        r : P r.
  unfold Router' in *.
  refine (sum_rect' _ _ _ e (fun p=>_) r).
  unfold internal' in *.
  exact (prod_rect' _ _ (fun p=>P (inr' IP p)) i p).  
Defined.

(**
Unfortunatelly, this scheme cannot be generalized for all inductive
types. The main problem are recursive types (we also need to assume an
inductively defined Empty_set and unit).
**)

Inductive nat' :=
| O' : nat'
| S' : nat' -> nat'.

Definition nat'' : Type.
  refine (unit + _) % type.
  (** what should go here? **)
Abort.

End Sugar.


Section Logic.
(*** Types as Logic (Curry-Howard) ***) 

(**
Curry howard tells us that types and logic are closely related. 
**)

(**
product ~ conjunction
**)

Print prod.
Print and.
(*
  Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B
  Inductive and  (A B : Prop) : Prop :=  conj : A -> B -> A /\ B 
*)

(**
sum ~ disjunction
**)

Print sum.
Print or.
(*
  Inductive sum (A B : Type) : Type := inl       : A -> A + B  | inr       : B -> A + B
  Inductive or  (A B : Prop) : Prop := or_introl : A -> A \/ B | or_intror : B -> A \/ B
*)

(**
dependent product / simga type ~ existential
**)

Print sigT.
Print sig.
Print ex.
(*
  Inductive sigT (A : Type) (P : A -> Type) : Type := existT   : forall x : A, P x -> sigT P
  Inductive sig  (A : Type) (P : A -> Prop) : Type := exist    : forall x : A, P x -> {x | P x}
  Inductive ex   (A : Type) (P : A -> Prop) : Prop := ex_intro : forall x : A, P x -> exists x, P x
*)
End Logic.


Section Collection.
(*** Types as Collections ***)

(**
Types can be interpreted as collections (e.g. sets).
Let us define some example collections.
**)

Inductive X : Set := x | x'.
Inductive Y : Set := y | y' | y''.
Inductive Z : Set := z.

Inductive I : Set := ix | iy | iz.
Definition choose := I_rect (fun _=>Set) X Y Z.

(**
prod ~ binary carthesian product
**)

Check (x, y') : X * Y. 

(**
sum ~ binary disjoint union / dependent carthesian product with bool
**)

Check inl _ x   : X + Y.
Check inr _ y'' : X + Y.

(**
dependent product ~ disjoint union / binary dependent carthesian product

U i:I, choose i 
(x:X * Y)
**)

Check existT _ ix x  : {i:I & choose i}.
Check existT _ iy y' : {i:I & choose i}.
Check existT _ iz z  : {i:I & choose i}.

Check existT _ x y  : {_:X & Y}.

(**
sigma type ~ subset

Because of proof irrelevance, a Prop has either zero or one
inhabitants.
**)

Lemma lma : 3 <= 5. auto. Qed.

Check exist _ 3 lma : {n:nat | n <= 5}.

(**
We can use disjoint unions to simulate subsets.
**)

Check existT _ 3 tt : {n:nat & if leb n 5 then unit else Empty_set}.

(**
Existentials seem to play a crucial role in a set interpretation of
types. So what does the dual of existential --- forall --- do?

Church Encodings use foralls and form sets of certain sizes, but this
fact seem to be unprovable in Coq.
**)

Definition emptySet := forall S:Set, S.

Definition oneSet := forall S:Type, forall _:S, S.
Print oneSet.
Definition oneSetA : oneSet := fun _ e => e.

Definition twoSet := forall S:Type, forall _:S, forall _:S, S.
Print twoSet.
Definition twoSetA : twoSet := fun _ e _ => e.
Definition twoSetB : twoSet := fun _ _ e => e.

Definition countableSet := forall S:Type, forall _:S, forall _:(forall _:S, S), S.
Definition three : countableSet := fun _ z s => s (s (s z)).

(**
forall ~ carthesian product

The number of element depend on parametricity / functional
extensionality. In CoC is likely unproofable how many elements there
are in such a set.
**)

Check (fun i => match i return choose i with
  ix => x | iy => y | iz => z
  end) : (forall i:I, choose i).

Check (fun i => match i return choose i with
  ix => x' | iy => y | iz => z
  end) : (forall i:I, choose i).


(**
We can access an element of the cross-product via function
application:
**)
Goal (fun i => match i return choose i with
  ix => x | iy => y' | iz => z
  end) (iy) = y'.
  trivial.
Qed.

(**
We can build binary products using bool ...
**)

Check (fun b => match b return (if b return Set then X else Y) with
  true  => x | false => y'
  end) : forall b:bool, if b then X else Y.

(**
... but not bool'.
**)
Goal forall b:bool', b _ X Y.
  refine (fun b => b  _ _ _).
  - (** because of parametricity, we know that b can only return X or
        Y, but proofing that in Coq is another story.

        The takeaway here is the following: Predicting what kind of
        elements there are in a set is hard (likely undecidable),
        because it depends on what is proofable in Coq.
     **)
Abort.

(** 
In a typed language, the usual operations on sets are only sensible
for sets that contains elements of the same type. The following
operations are defined on the sets {a:A | P a} and {a:A | Q a}.
**)

Definition union A (P Q:A->Prop) := {a:A | P a \/ Q a}.
Definition intersection A (P Q:A->Prop) := {a:A | P a /\ Q a}.
Definition subtraction A (P Q:A->Prop) := {a:A | P a /\ not (Q a)}.
Definition complement A (P:A->Prop) := {a:A | not (P a)}.

Definition powerset A := {P:A->Prop & {a:A | P a}}.
