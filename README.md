# Data Types a la Carte in Idris

A brief discussion on design choices implementing DTalC.

## Syntax

One of the problems with the [original Data Types a la Carte implementation](http://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf),
was that the coproduct, `(:+:)`, allowed arbitrary grouping of signatures,
e.g. `(f :+: g) :+: g`. However, injection only performed a linear search from
left to right, and so the subtyping relation could not be satisfied in cases
which were not right-associative, such as `f :≺: (f :+: g) :+: h`.

To remedy this, a [list of signatures can be used instead](https://reasonablypolymorphic.com/blog/better-data-types-a-la-carte/).
For example, `f :+: g` would be written as `Sig [f, g]`, using `Sig` below.
Here, `fs` is a list of the different signatures that make up the composite
signature `Sig`. The `a` is the type given to each `f` in `fs`.

(Side note: An alternative method to solve injection into non-right-associative
signatures involves using a [backtracking search](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.643.3533&rep=rep1&type=pdf),
but using a list provides a simpler solution)


```idris
data Sig : (fs : List (Type -> Type)) -> (a : Type) -> Type where
    Here  : f a -> Sig (f :: fs) a
    There : Sig fs a -> Sig (f :: fs) a
```

Instead of `InL` and `InR` constructors for the coproduct, `Sig` uses `Here`
and `There` to describe how to construct a value of a signature. For example,
the DSL from Data Types a la Carte paper can be described as:

```idris
data Val k = V Int
data Add k = A k k
```

Using the standard definition of Fix, and the `Here` and `There` constructors,
DSLs containing both values and addition can be created. Below represents the
expression `1 + 2`:

```idris
ex1 : Fix (Sig [Val, Add])
ex1 = In (There (Here (A x y))) where
    x = In (Here (V 1))
    y = In (Here (V 2))
```

Clearly, this is very cumbersome to write, and so, like in the original paper,
it would be better to automate injection into some super-type. This will involve
finding the correct combination of `There` and `Here`.

Attempting to use interface instances, like in the original paper, such as
those below to perform this linear-search requires overlapping instances, which
Idris [does not allow](http://docs.idris-lang.org/en/v0.9.18/tutorial/classes.html).

Therefore, another solution to this search is required. Fortunately, this has
already been solved in the standard library (see `Elem` in [Data.List](https://github.com/idris-lang/Idris-dev/blob/master/libs/base/Data/List.idr)),
with a structure similar to `Elem` below.

The constructor `H` is a proof the signature `f` is at the front of the list
of signatures to be composed together, `fs`. The constructor `T` is a proof the
signature is after the front of the list.

```idris
data Elem : (f : Type -> Type) -> (fs : List (Type -> Type)) -> Type where
    H : Elem f (f :: fs)
    T : Elem f ys -> Elem f (y :: ys)
```

Using this, an `inj` function can be created to construct a sequence of `Here`
and `There`:

```idris
inj' : Elem f fs -> f a -> Sig fs a
inj' H     x = Here x
inj' (T t) x = There (inj' t x)
```

However, this does not currently provide any advantage over manually using
`Here` and `There`, since `inj'` requires manually specifying `H` and `T`.
However, Idris' automatic proof search can be leveraged to have it automatically
find the correct combination of `H` and `T`:

```idris
inj : {auto prf : Elem f fs} -> f a -> Sig fs a
inj {prf=H}   x = Here x
inj {prf=T t} x = There (inj {prf=t} x)
```

For convenience, `inj` can be adapted to work with `Fix`:

```idris
inject : {auto prf : Elem f fs} -> f (Fix (Sig fs)) -> Fix (Sig fs)
inject = In . inj
```

Putting this together, smart constructors can be created for the example DSL.
Instead of a type constraint, `Val :<: f`, such as in the original paper,
`Elem Val fs` is used to prove that `Val` exists in `fs`:

```idris
val : {auto prf : Elem Val fs} -> Int -> Fix (Sig fs)
val x = inject (V x)

add : {auto prf : Elem Add fs} -> Fix (Sig fs) -> Fix (Sig fs) -> Fix (Sig fs)
add x y = inject (A x y)
```

Putting this all together, DSLs containing values and addition can be succinctly
represented:

```idris
ex2 : Fix (Sig [Val, Add])
ex2 = add (val 1) (add (val 2) (val 3))
```

## Semantics

In the original paper, typeclasses provide a method to specify the semantics
of different pieces of syntax separately, by providing an algebra `f a -> a`
to fold over a fix tree `Fix f`.

In order to fold over a `Fix` tree using `cata`, a `f` needs to be a functor:

```idris
cata : Functor f => (f a -> a) -> Fix f -> a
cata alg = alg . map (cata alg) . inop
```

In this implementation `f` is `Sig fs`, therefore, `Sig fs` needs to be a
functor. This *could* be done by modifying the definition of `Here` to be
`Here : Functor f => f a -> Sig (f :: fs) a`. However, in the implementation
so-far no functions have required `f` to be a functor and so this solution feels
sub-optimal.

Instead, the functor instance for `Sig fs` will be defined inductively such that
`Sig fs` will be a functor when each `f` in `fs` has its own definition of functor.

Firstly, where there are no signatures it is not possible to map over anything:

```idris
Functor (Sig []) where
    map _ (Here _) impossible
    map _ (There _) impossible
```

For the base case, `Here`, `map func x` calls `map : (a -> b) -> f a -> f b`.
Whereas, in the recursive case, `There`, `map func t` calls
`map : (a -> b) -> Sig fs a -> Sig fs b`.

```idris
(Functor f, Functor (Sig fs)) => Functor (Sig (f :: fs)) where
    map func (Here x) = Here (map func x)
    map func (There t) = There (map func t)
```

Continuing the example, by defining functor instances for both values and
addition, `Sig [Val, Add]` is also a functor.

```idris
Functor Val where
    map f (V x) = V x

Functor Add where
    map f (A x y) = A (f x) (f y)
```

In order to define the algebra `f a -> a` for a signature `f`, an interface is
used to allow the algebra for different pieces of syntax to be defined separately.

```idris
interface Alg (f : Type -> Type) (a : Type) where
    alg : f a -> a
```

Using the same technique used to define the `Functor` instance for `Sig`, the
`Alg` instance will be defined for `Sig fs`, provided each `f` in `fs` has its
own `Alg` instance. Again, when there is no syntax it is not possible to
use the algebras of any signatures:

```idris
Alg (Sig []) a where
    alg (Here _) impossible
    alg (There _) impossible
```

In the base case, `alg x` uses `alg : f a -> a`. The recursive case uses
`alg : Sig fs -> a`.

```idris
(Alg f a, Alg (Sig fs) a) => Alg (Sig (f :: fs)) a where
    alg (Here x) = alg x
    alg (There x) = alg x
```

To continue the expression example, `Alg` instances can be created that
translate into a result integer:

```idris
Alg Val Int where
    alg (V x) = x

Alg Add Int where
    alg (A x y) = x + y
```

Given signatures which have an algebra to which converts their syntax to
integers, a `calc` function can be created which calculates the value of an
expression:

```idris
calc : (Functor (Sig fs), Alg (Sig fs) Int) => Fix (Sig fs) -> Int
calc = cata alg
```

## Summary

This demonstrates how Data Types a la Carte can be implemented in such as
way as to solve one of the original problems. This shows how the inability to
create overlapping instances is solved by using the `Elem` type, and how
automatic proof search can be used to automatically inject into a type.

## Related Work: Effect Handlers

A problem inherent with Data Types a la Carte is it inability to allow
different semantic domains to be easily composed. To extend the DSL presented
with exceptions, for example, would require reimplementing the interface
instances `Alg Val Int` and `Alg Add Int` to be `Alg Val (Either Err Int)` and
`Alg Add (Either Err Int)`. One solution to this is [Effect Handlers](http://okmij.org/ftp/Haskell/extensible/extensible-a-la-carte.html)
which handle only specific parts of the syntax composed, instead of *all* the
syntax at once. Fortunately, this has [already been implemented in Idris](http://docs.idris-lang.org/en/latest/effects/introduction.html).
