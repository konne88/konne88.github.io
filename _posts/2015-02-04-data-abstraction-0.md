---
content_type: md
layout: main
header_style: max-height:50px;
click: download('/')
title: Konstantin Weitz
comments: true
info:
---

Abstract Data Types and Object Oriented Programming in Coq (Part I)
-------------------------------------------------------------------

This post describes how to use data abstractions, specifically Abstract Data Types (ADTs) and Object Oriented Programming (OOP), to hide a value's representation in a functional programming language with dependent types.
<!--more-->
Many of the ideas in this post are based on [TaPL, Chapter 24.2 and 32][TAPL] and [Cook][COOK]. You can download the source code of this post's [Coq][COQ], [Haskell][HASK], and [Java][JAVA] examples.

### Abstract Data Types

In a language with [parametric polymorphism][POLY] and [parametricity][PARA]
(the inability to inspect type variables), _type variables_ can be used to hide a value's representation. In the following example, the type variable `A` hides `a`'s representation from the function `id`:

    Definition id A (a:A) := a.

Some functions require additional parameters to _operate on_ (create, observe, combine, and reason about) values with hidden representations.  For example:

    Definition min A (le:A->A->bool) (a b:A) :=
      if le a b then a else b.

Frequently used operations are packaged with their type variable using an _existential type_ --- such a package is called Abstract Data Type (ADT). For example:

    Record Order := {
      A  : Type;
      le : A -> A -> bool
      (* antisymmetry, transitivity, and totality are elided *)
    }.
    
    Record IntSet := { 
      A        : Type; 
      contains : A -> nat -> bool;                     (* observe *)
      empty    : A;                                    (* create *)
      emptyOk  : forall n, contains empty n = false;   (* reason  *)
      union    : A -> A -> A;                          (* combine *)
      unionOk  : forall n a b, contains (union a b) n = 
                               contains a n && contains b n
    }.
    
    Record Monoid := {
      A   : Type;
      add : A -> A -> A;
      one : A;
      _   : forall a, add a one = a;
      _   : forall a, add one a = a;
      _   : forall a b c, add (add a b) c = add a (add b c)
    }.

Instead of a type variable and additional parameters, a function can require an ADT to operate on values with hidden representations.  For example:

    Definition min (o:Order) (a b:A o) : A o :=
      if le o a b then a else b.
    
    Definition natOrder := {| A:=nat; le:=leb |}.
    
    Compute (min natOrder 9 3).

_Type classes_ remove some of the boilerplate associated with ADTs.  In Coq, the syntax for type classes is:

    Class Order := {
      A  : Type;
      le : A -> A -> bool
    }.
    
    Definition min `{Order} (a b:A) : A :=
      if le a b then a else b.
    
    Instance natOrder : Order := {| A:=nat; le:=leb |}.
    
    Compute (min 9 3).

In Haskell, the syntax for type classes is:

    class Ord a where
      (<=) :: a -> a -> Bool
    
    instance Ord Int where
      (<=) = (Prelude.<=)
    
    min :: forall a. Ord a => a -> a -> a
    min x y = if x <= y then x else y
    
    min 9 3


### Object Oriented Programming

In a language with _procedural abstraction_ (the inability to inspect function implementations), _functions_ can be used to hide a value's representation.  In the following example, the function `s` hides its representation from the function `contains`.

    Definition contains (n:nat) (s:nat -> bool) := s n.

The type of a function that hides a value's representation is called an _interface_. In the above example, the function `s` implements the `IntSet`interface, which consists of one method that tests whether the set contains a certain element.

    Definition IntSet := nat -> bool.

An interface's implementation is called an _object_. For example:

    Definition emptySet : IntSet := fun _ => false.
    
    Definition evenSet : IntSet :=
      fix R n := match n with 
      | 0 => true
      | 1 => false
      | S (S n) => R n
      end.

Functions that create objects are called _constructors_. For example:

    Definition listSet (l:list nat) : IntSet := fun n => contains l n.
    
    Definition treeSet (t:Tree) : IntSet := fun n => search n t.

The following example shows how to implements the set $$\{1,3,4,6,9,11\}$$ using both the `listSet` and `treeSet` constructor:

    Definition someListSet : IntSet := listSet [1;3;4;6;9;11].
    
    Definition someTreeSet : IntSet := treeSet
      (node 6 
        (node 3 
          (node 1 leaf leaf)
          (node 4 leaf leaf))
        (node 9 leaf
          (node 11 leaf leaf))).

The `IntSet` interface hides the implementation of an object. The `someListSet` and `someTreeSet` are therefore indistinguishable:

    Goal someListSet = someTreeSet. 
      apply functional_extensionality.
      intro n.
      do 12 (destruct n; auto).
    Qed. 

There is no universally accepted definition of _Object Oriented Programming_, but the above definitions of interface, object, and constructor capture the essence of OOP (in my opinion). [Cook][COOK], and to some extend [Odersky][ODERSKY-TALK] (see [slide 4][ODERSKY-SLIDES]), motivate this definition of OOP, and show how to implement other common OOP constructs with it.

An interface might require multiple methods. This can be encoded with an extra parameter that selects the method. For example, a pair can be defined as:

    Inductive PairMethod := fst | snd.
    
    Definition BoolNatPair : Type := forall m:PairMethod, 
      match m with fst => bool | snd => nat end.
    
    Definition makePair a b : BoolNatPair := fun m => match m with
      | fst => a
      | snd => b
      end.
    
    Compute (makePair true 8) fst.
    Compute (makePair true 8) snd.

The above examples can be implemented in Java as follows (constructors are implemented with classes):

    interface IntSet {
      boolean contains (int n);
    }
    
    class evenSet implements IntSet {
      public boolean contains (int n) {
        return n % 2 == 0;
      }
    }
    
    class listSet implements IntSet {
      private int[] l;
    
      public listSet (int[] l) {
        this.l = l;
      }
    
      public boolean contains (int n) {
        return Arrays.asList(l).contains(n);
      }
    }
    
    interface BoolNatPair {
      boolean fst();
      int snd();
    }
    
    class makePair implements BoolNatPair {
      private boolean a;
      private int b;
    
      public makePair(boolean a, int b) {
        this.a = a;
        this.b = b;
      }
    
      public boolean fst() {
        return a;
      }
    
      public int snd() {
        return b;
      }
    }

The example interfaces so far only contain operations to observe an object. ADTs also provide operations to create, combine, and reason about values. Can interfaces be extended to include these operations? The answer is _no_. Consider the following example:

    Inductive IntSetMethod := contains | isEmpty | isEmptyOk | empty | union.

    Definition IntSet : Type.
    refine (forall m:IntSetMethod, match m with
    | contains => nat -> bool
    | isEmpty  => bool          (* observe *)
    | isEmptyOk => _            (* reason  *)
    | empty => _                (* create  *)
    | union => _                (* combine *)
    end).
    - (* Cannot refer to object: forall n, this contains n = false *) admit.
    - (* Cannot refer to type:   IntSet *) admit.
    - (* Cannot refer to type:   IntSet *) admit.
    Abort. 

Adding the observation operation `isEmpty` is successful. Adding the operation `isEmptyOk` to reason about `isEmtpy` fails, as we cannot refer to the current object (`this`). Adding operations to create (`empty`) and combine (`union`) objects fails, as we cannot refer to the interface `IntSet` that is currently being defined. Using `Fixpoint` instead of `Definition` to make `IntSet` self-referential fails, as there is no value to induct on.

Instead of extending the interface, operations to create and combine objects can be defined as constructors. For example:

    Definition union (s:IntSet) (t:IntSet) : IntSet :=
      fun n => s n || t n.

One can reasoning about these constructors by unfolding their definitions. Reasoning about operations that observe an object (e.g. `isEmpty`) appears to be impossible.

### Coming Next

In this post, I have defined OOP in its purest form. I the next post, I will explore the consequences of adding more structure to interfaces (for example, defining an interface to be a record of methods).

There are limitations to ADTs and OOP. For example, performance concerns can bloat the number of operations (e.g. `batchInsert`), or limit the flexibility of an ADT/interface. In the next post, I will describe these limitations, and explore alternatives such as: domain specific languages, compilers, and synthesis (e.g. [FIAT][ADT-SYN-PAPER]) which decompose functionality & optimizations instead of data structures & algorithms.

[TAPL]: http://www.cis.upenn.edu/~bcpierce/tapl
[POLY]: https://en.wikipedia.org/wiki/Parametric_polymorphism
[PARA]: https://en.wikipedia.org/wiki/Parametricity 
[COOK]: http://dl.acm.org/citation.cfm?id=1640133
[ODERSKY-SLIDES]: http://www.slideshare.net/Typesafe/scaladays-keynote
[ODERSKY-TALK]: https://www.youtube.com/watch?v=iPitDNUNyR0
[ADT-SYN-PAPER]: https://people.csail.mit.edu/jgross/personal-website/papers/2015-adt-synthesis.pdf

[COQ]:  {{ site.url }}/assets/posts/data-abstraction/data-abstraction.v
[JAVA]: {{ site.url }}/assets/posts/data-abstraction/data-abstraction.java
[HASK]: {{ site.url }}/assets/posts/data-abstraction/data-abstraction.hs
