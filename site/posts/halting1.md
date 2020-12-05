---
title: "The Halting Problem (part 1)"
author: Callan McGill
date: "Dec 4, 2020"
tags: [Halting Problem, Haskell]
description: Exploring the Halting problem in Haskell
quote: \'Begin at the beginning,\' the King said, very gravely, \'and go on till you come to the end&#58; then stop.\'
quoteAuthor: Lewis Carroll, Alice in Wonderland

---

The halting problem states, informally, that there is no algorithm to determine whether an _arbitrary_ program, when provided with some given input, will halt.
Even for specific programs this can lead to interesting unsolved questions.
A well-known example is the
[Collatz conjecture](https://en.wikipedia.org/wiki/Collatz_conjecture), which states, that the
following function halts for all inputs:
```haskell
collatz :: Natural -> Bool
collatz 1 = True
collatz n | even n    = collatz (n `div` 2)
collatz n | otherwise = collatz (3 * n + 1)
```
```terminal
> all id (fmap collatz [1..10000])
True
```

Typically, the halting problem is formalised by first picking some specific theory of computation,
and then demonstrating, within that theory, that no such halting algorithm can be written.
Unfortunately, the theory typically chosen is that of Turing machines. These are
hard to formalise ([Wikipedia](https://en.wikipedia.org/wiki/Turing_machine#Formal_definition)
informs me, for example, that "a (one-tape) Turing machine can be formally defined
as a [certain] 7-tuple"!)
and don't offer a particularly good foundation for programming. A Turing
machine, after all, is _not_ a programming language and is also not a particularly good
machine model either!

Instead let's take an alternative approach: we will use the lambda calculus
as the basis for computation. The lambda calculus is both a programming language in itself
and the foundation of all other functional languages.
As a testament to this idea, we will first prove halting for the lambda calculus
and then see how the same argument looks when transplanted to Haskell.
Finally, in the [next post](https://boarders.github.io/posts/halting2.html) we will formalise
the argument in Agda and fill in most of the lingering details we brush aside here.

In the setting of the lambda calculus, a precise statement of halting can be given thusly:

**Theorem ($\lambda$-Halting)**: There does not exist a $\lambda$-term
$\def\h{\mathbf{HALT}} \def\s{\text{ }} \def\L{\mathrm{L}} \def\l{\mathrm{l}} \def\true{\mathbf{true}}
\def\false{\mathbf{false}} \h$ such that for any given lambda term
$\L$,  $\h \text{ } \L$ evaluates to $\true$ when $\L$ terminates and $\false$ otherwise.

Here, by termination, we mean what is otherwise called normalization. A term
is normalizing if there exists a finite sequence of
[$\beta$-reductions](https://en.wikipedia.org/wiki/Lambda_calculus#%CE%B2-reduction_2)
(performed anywhere within the term)
after which, the term contains no further $\beta$-redexes.
A well-known result in the study of the lambda calculus says that a term normalizes if
and only if it normalizes when we always pick the leftmost, outermost redex.
This gives us an algorithm that will _confirm_ that a given term does indeed terminate
but will never disconfirm whether a term loops indefinitely. In other words,
this gives a
[semi-decision procedure](https://en.wikipedia.org/wiki/Decidability_(logic)#Semidecidability)
for halting.

Let's turn to the proof of $\lambda$-Halting. The arguments here are adapted from the introduction
to
[Computational foundations of basic recursive function theory](https://www.sciencedirect.com/science/article/pii/0304397593900858)
by Constable and Smith. Essential to this argument is that lambda calculus
allows us to encode arbitrary recursive functions.
Such recursion is performed by fixed-point combinators. We will make use of perhaps
the most well-known fixed-point combinator (though any other would do for our purposes), the
[$\mathrm{Y}$-combinator](https://en.wikipedia.org/wiki/Fixed-point_combinator#Y_combinator),
defined as follows:

$$
\def\Y{\mathrm{Y}}
\def\mr#1{\mathrm{#1}}
\def\la#1{\lambda \s \mathrm{#1} \s . \s }
\def\ap#1#2{\mathrm{#1} \s {\mathrm{#2}}}
\def\be{\mapsto_{\beta}}
\Y = \la{f} \ap{(\la{x} \ap{f}{(\ap{x}{x})})}{(\la{x} \ap{f}{(\ap{x}{x})})}
  $$

The key property that fixed-point combinators satisfy is that
for any lambda term $\rm{g}$ we have that $(\ap{\Y}{\rm{g}})$ is a fixed point for
$\rm{g}$ in the sense that $\ap{g}{(\ap{\Y}{g})}$ is $\beta$-equivalent to $\ap{\Y}{g}$.
This is straightforward to see as follows:

  $$
     \begin{aligned}
      \ap{\Y}{g} \be \; &\ap{(\la{x} \ap{g}{(\ap{x}{x})})}{(\la{x} \ap{g}{(\ap{x}{x})})} \\
                 \be \; &\ap{g}({\ap{(\la{x} \ap{g}{(\ap{x}{x})})}{(\la{x} \ap{g}{(\ap{x}{x})})}}) \\
        \equiv_\beta \; &\ap{g}{(\ap{Y}{g})}
    \end{aligned}$$

Fixed point combinators allow us to write recursive functions. For example, supposing we
have already [encoded](https://en.wikipedia.org/wiki/Church_encoding) Booleans and Natural numbers
as certain lambda terms, then in a language which allowed recursive definitions we could write:
$$
  \mathrm{fact} (n) = \mathrm{if}\; n = 0\;
                        \mathrm{then} \; 1 \;
                        \mathrm{else} \; n * \;\mathrm{fact} (n - 1)
$$
In the lambda calculus we can't refer to the variables we are defining in their body and so
instead we make use of a fixed point combinator like so:
$$
  \mathrm{fact} = \Y ( \la{f} \la{n} \mathrm{if}\; n = 0\;
                        \mathrm{then} \; 1 \;
                        \mathrm{else} \; n * f \; (n - 1))
$$

Given this, and supposing we are given such a $\h$ term as above. We then introduce the
following terms:

  $$
     \begin{aligned}
        \bot  & = \ap{Y}{(\la{x}x)} \\
        \rm{p}& = {\la{f}\text{if $(\ap{\h}{f})$ then $\bot$ else true}} \\
        \rm{d}& = \ap{Y}{p}
  \def\betaStep{\mapsto_{\beta}}
      \end{aligned}  $$

The suggestively named $\bot$ is an infinitely looping expression:

  $$
     \begin{aligned}
      \ap{\Y}({\la{x}x}) \be \;
        &  \ap{(\la{x} x)}(\ap{\Y}({\la{x}x})) \\
        \be \; &{\ap{Y}{(\la{x}x})}
    \end{aligned}$$

The term $\rm{p}$ takes any argument $\mathrm{f}$ and returns true
if the argument doesn't terminate and otherwise loops forever.
We then define $\mathrm{d}$ as the fixed point of this function.
With ordinary recursion we would write this as follows:

$$
  \rm{p} = \text{if } (\ap{\h}{\rm{p}}) \text{ then } \bot \text{ else  true}
$$

Intuitively, we can see the problem with this term - if it halts then it reduces to
$\bot$ and if it doesn't halt then it reduces to $\mathrm{true}$.
In slightly more detail:

  - if $\ap{\h}{d}$ is $\rm{true}$ then:
      $$
     \rm{d} \equiv_\beta \ap{p}{d} :\equiv
       \text{if $(\ap{\h}{d})$ then $\bot$ else true} \betaStep \bot
     $$
    We therefore have that $\rm{d}$ does not terminate and so $\ap{\h}{d}$ must be $\rm{false}$.
  - Similarly if $\ap{\h}{d}$ is $\rm{false}$ then:
      $$
     \rm{d} \equiv_\beta \ap{p}{d} :\equiv
       \text{if $(\ap{\h}{d})$ then $\bot$ else true} \betaStep \text{true}
      $$
      and so we get that $\rm{d}$ terminates and so we get that $\ap{\h}{d}$ is true.


Let us see how easily these concepts translate to a language like Haskell.
Note that in Haskell all types are _partial_ (using Constable's terminology).
This means that every type is inhabited by some
non-terminating term which is typically denoted $\bot$ (analogous to the term considered above).
Reformulating the theorem with this in mind we get:

**Theorem (Haskell-Halting)**: In Haskell there is no function $\mathbf{halt}$ with the following behaviour:
```haskell
halt :: Nat -> Nat
halt ⊥ = 0
halt _ = 1
```

Of course, this specification is not legal Haskell (and moreover we are claiming that no function
can have this behaviour). This formulation may appear slightly different
to the Halting problem insomuch as we are only considering the (partial) natural numbers, but
we can observe that for any `f :: Nat -> Nat` we can use
`halt (f n)` to determine if `f` halts on input `n` and so this would
allow us to determine on which inputs `f` terminates.

In order to mimic the argument above, let's use a fixed point function similar to $\Y$, aptly named
[$\mathrm{fix}$](https://hackage.haskell.org/package/base-4.14.0.0/docs/Data-Function.html#v:fix):
```haskell

fix :: (a -> a) -> a
fix f = let x = f x in x
```


We note that $\rm{fix}$ satisfies precisely the same fixed-point property as $\Y$:
$$
  \ap{f}{(\ap{fix}{f})} \equiv_\beta \ap{fix}{f}
  $$

As in the lambda calculus, $\mathrm{fix}$ allows us to capture all forms of recursion in a
single function. For instance, if we define an "openly recursive" sum function:
```haskell
{-# LANGUAGE LambdaCase #-}

sumR :: forall n . (Num n) => ([n] -> n) -> ([n] -> n)
sumR recFn = \case
  []     -> 0
  (x:xs) -> x + recFn xs
```
Then taking $\mathrm{fix}$ recovers the usual sum:
```haskell
mySum :: forall n . (Num n) => [n] -> n
mySum = fix sumF
```
```shell
> mySum [1..100]
5050
```

Recasting our problem terms from earlier we get:

```haskell
bottom :: a
bottom = fix id

p :: Natural -> Natural
p n = if halt n == 0 then 1 else bottom

d :: Natural
d = fix p
```

As above let us think about the value of $(\ap{h}{problem})$:
```haskell
    d
  ≡ fix d
  ≡ p d
  ≡ if halt d == 0 then 1 else bottom
```

As before:

  - If `halt d` is $0$ then it is 1.
  - If `halt d` is $1$ then it is 0.


We therefore conclude that no such function `h` can be written in Haskell and so we cannot tell
(in general) whether a term of type $\mathrm{Natural}$ will diverge or not. We should note that
there is nothing
special about $\mathrm{Natural}$ in this argument and we could have picked any type containing at
least two distinct terms along with some ability to compare terms for equality.

Thank you for reading! Hopefully this has demonstrated the unity of ideas between the lambda calculus and a functional language like
Haskell and the naturality of studying computability theory from this perspective. In the [next post](https://boarders.github.io/posts/halting2.html), we will formalise this argument in Agda.
