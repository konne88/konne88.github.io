---
content_type: md
layout: main
header_style: max-height:50px;
click: download('/')
title: Konstantin Weitz
info:
---

The Natural Number, Type, Set, and Proposition Correspondence
-------------------------------------------------------------

In this post, I'm showing connections between natural numbers, types, sets and
propositions. This is similar to the [Curry Howard correspondence][CURRY] which 
shows a connection between functional programming languages and propositions, or 
[Chris Taylor's blog post][CHRIS] which explains how the natural numbers are 
connected to Haskell types.

<!--more-->

Let us define that a natural number $$n$$ is related to a

- type $$T$$ iff $$ n = \text{number of terms inhabiting } T $$
- set $$S$$ iff $$ n = \vert S \vert $$
- proposition $$P$$ iff $$ n > 0 \iff P $$

In the following table, the natural number of each row is related to 
all other cells in the row (assuming the inputs $$A$$, $$B$$, ... are related).

Consider for example the 5th row.
For the arbitrary natural number $$A=3$$, and the related type `data A = a | b | c`,
$$ S(3) $$ is related to `Maybe A`.

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
$$ \vert S \vert $$: [cardinality][CARD], and
$$ [0,n] $$:         [interval][INTV].

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

<br/><br/>
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
