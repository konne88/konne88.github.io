---
content_type: md
layout: main
header_style: max-height:50px;
click: download('/')
title: Konstantin Weitz
info:
---

Connections between Natural Numbers, Types, Sets, and Propositions
------------------------------------------------------------------

This post shows connections between natural numbers, types, sets and propositions. This post draws ideas from the [Curry Howard correspondence][CURRY] which shows a connection between functional programs and mathematical proofs, and [Chris Taylor's blog post][CHRIS] which shows a connection between natural numbers and Haskell types.

<!--more-->

Intuitively, we will say that a natural number $$n$$ is _related_ to the type, set, or proposition $$a$$ if and only if the "size" of $$a$$ is equal to $$n$$. More formally, a natural number $$n$$ is related to:

- _Type_ $$T$$        iff $$ n = \text{number of terms inhabiting } T $$
- _Set_ $$S$$         iff $$ n = \vert S \vert $$
- _Proposition_ $$P$$ iff $$ n > 0 \iff P $$

The following table shows related natural numbers, types, sets, and propositions. The natural number in the leftmost cell of each row is related to all other cells in the row, assuming that the inputs $$A$$, $$B$$, and $$S_a$$ are already related.

Consider for example the two leftmost cells in the 5th row, and assume that $$A=3$$ and `data A = a | b | c`. 
$$A$$ and `A` are related, because `A` is inhabited by the $$3$$ terms: `a`, `b`, and `c`. Therefore, the table shows that $$S(A)$$ and `Maybe A` are related as well. This is indeed the case, because `A` is inhabited by the $$4$$ terms: `Just a`, `Just b`, `Just c`, and `Nothing`.

Natural Number              | Type           | Set                        | Proposition
----------------------------|----------------|----------------------------|------------------
 $$ 0 $$                    | `Void`         | $$ \emptyset $$            | $$ \bot $$ 
 $$ 1 $$                    | `()`           | $$ \{ a \} $$              | $$ \top $$ 
 $$ 2 $$                    | `Bool`         | $$ \{ a,b \} $$            | $$ \top $$ 
                            | `Nat`          | $$ \mathbb{N} $$           | $$ \top $$
 $$ S(A) $$                 | `Maybe A`      |                            | 
 $$ A + B $$                | `Either A B`   | $$ A \uplus B $$           | $$ A \vee B $$
 $$ A \cdot B $$            | `(A,B)`        | $$ A \times B $$           | $$ A \wedge B $$
 $$ B^A $$                  | `A -> B`       | $$ B^A $$                  | $$ A \implies B $$
 $$ \sum_{a:[0,A]}{S_a}  $$ | `{a:A & S a}`  | $$ \biguplus_{a:A}{S_a} $$ | $$ \exists_{a:A}{S_a} $$
 $$ \prod_{a:[0,A]}{S_a} $$ | `(a:A) -> S a` |                            | $$ \forall_{a:A}{S_a} $$

Some of the less known symbols are
$$ \times $$:        [cartesian product][CROSS],
$$ \uplus $$:        [disjoint union][UPLUS],
$$ \{ a \} $$:       [singleton][SINGL],
$$ S(n) $$:          [successor][SUCC],
$$ \vert S \vert $$: [cardinality][CARD],
$$ [0,n] $$:         [interval][INTV], and
`(a:A) -> S a`:      [dependent function][DEP]
.

There are a couple of holes in the table. Most are straight forward to fill in,
they just don't seem to have a dedicated symbol. The hole in
the natural numbers can be filled in with $$\aleph_0$$ if we consider the 
[cardinal numbers][CARDINAL].

Why is it useful to know these correspondences? 

One reason is that it allows us to use the reasoning strategies from one domain,
and to apply them to another one. In a proof assistant like Coq, we might be
able to take a powerful tactic like `omega`, and apply it to reasoning about the
size of sets.

It also allows us to decipher seemingly arbitrary overloading of mathematical
operators. For a long time I, for example, didn't understand why
mathematicians decided to use $$\cdot$$ to mean $$\wedge$$.

Thinking about correspondences also allows us to make good definitions for corner
cases. For example, in the domain of numbers, it is not entirely clear
what $$0^0$$ should be, as 
  $$\lim_{x \to 0}{0^x} = 0$$ and 
  $$\lim_{x \to 0}{x^0} = 1$$.
In the domain of propositions, on the other hand, it is obvious that
$$\bot \implies \bot$$ should be $$\top$$.

### Open Questions

In the above discussion, we realized that there are $$\prod_{a:A}{B_a}$$ ways
to implement `(a:A) -> B a` (for every `a`, our implementation can choose to
return any element in `B a`).

Using the same reasoning, we would expect that there is a huge number of 
implementations for the type `(T:Type) -> T` (for every element `T` in the 
"Set of all Sets", we can choose to return any element in `T`).
But, it turns out that there is, due to [parametricity][PARAM], no 
way to implement a function of this type. In fact, this type is the
[Church Encoding][CHURCH] of the empty type.

Similarly, there should be an uncountable number of ways to implement 
`Nat -> Bool` (see [Luke Palmer's blog][LUKE]). But we also know, due to the 
limited number of ascii characters, that there can only be countably many 
implementations.

[CURRY]: http://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
[CROSS]: http://en.wikipedia.org/wiki/Cartesian_product
[UPLUS]: http://en.wikipedia.org/wiki/Disjoint_union
[SINGL]: http://en.wikipedia.org/wiki/Singleton_(mathematics)
[SUCC]: http://en.wikipedia.org/wiki/Successor_function
[CARD]: http://en.wikipedia.org/wiki/Cardinality
[INTV]: http://en.wikipedia.org/wiki/Interval_(mathematics)
[PARAM]: http://en.wikipedia.org/wiki/Parametricity
[CHURCH]: http://en.wikipedia.org/wiki/Church_encoding
[LUKE]: http://lukepalmer.wordpress.com/2012/01/26/computably-uncountable/
[ORDINAL]: http://en.wikipedia.org/wiki/Ordinal_number
[CARDINAL]: http://en.wikipedia.org/wiki/Cardinal_number
[CHRIS]: http://chris-taylor.github.io/blog/2013/02/10/the-algebra-of-algebraic-data-types/
[DEP]: http://en.wikipedia.org/wiki/Dependent_type

<div id="disqus_thread"></div>
<script type="text/javascript">
    /* * * CONFIGURATION VARIABLES: EDIT BEFORE PASTING INTO YOUR WEBPAGE * * */
    var disqus_shortname = 'konne'; // required: replace example with your forum shortname

    /* * * DON'T EDIT BELOW THIS LINE * * */
    (function() {
        var dsq = document.createElement('script'); dsq.type = 'text/javascript'; dsq.async = true;
        dsq.src = '//' + disqus_shortname + '.disqus.com/embed.js';
        (document.getElementsByTagName('head')[0] || document.getElementsByTagName('body')[0]).appendChild(dsq);
    })();
</script>
