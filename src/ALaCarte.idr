module ALaCarte

import Fix

%access public export

||| Position of a sub-type in a super-type composed of signatures `fs`.
data Sig : (fs : List (Type -> Type)) -> (a : Type) -> Type where
    ||| The sub-type `f` is located at the head of the list of composed types `fs`.
    Here  : f a -> Sig (f :: fs) a
    ||| The sub-type is located after the head of the list.
    There : Sig fs a -> Sig (f :: fs) a

||| A proof that some signature `f` is found in a list `fs`.
data Elem : (f : Type -> Type) -> (fs : List (Type -> Type)) -> Type where
    ||| A proof the signature `f` is at the head of the list of signatures `fs`.
    H : Elem f (f :: fs)
    ||| A proof the signature `f` is after the front of the list.
    T : Elem f ys -> Elem f (y :: ys)

||| Inject some sub-type `f a` into a super type, `Sig fs a`, containing syntax
||| for `f a`, i.e. `Elem f fs`.
inj : {auto prf : Elem f fs} -> f a -> Sig fs a
inj {prf=H}   x = Here x
inj {prf=T t} x = There (inj {prf=t} x)

||| Inject some type `f a` into a `Fix` tree containing syntax for `f a`.
inject : {auto prf : Elem f fs} -> f (Fix (Sig fs)) -> Fix (Sig fs)
inject = In . inj

||| Base case making `Sig` an instance of `Functor`.
Functor (Sig []) where
    map _ (Here _) impossible
    map _ (There _) impossible

||| Recursive case making `Sig` an instance of `Functor`.
(Functor f, Functor (Sig fs)) => Functor (Sig (f :: fs)) where
    map func (Here x) = Here (map func x)
    map func (There t) = There (map func t)

||| Algebra used to fold over a `Fix` tree, creating a value of type `a`.
interface Alg (f : Type -> Type) (a : Type) where
    alg : f a -> a

||| Base case making `Sig` an instance of `Alg`.
Alg (Sig []) a where
    alg (Here _) impossible
    alg (There _) impossible

||| Recusrive case making `Sig` an instance of `Alg`.
(Alg f a, Alg (Sig fs) a) => Alg (Sig (f :: fs)) a where
    alg (Here x) = alg x
    alg (There x) = alg x

||| Convenience method for folding over a `Fix` tree using the algebra defined
||| in interface instances.
eval : (Functor f, Alg f a) => Fix f -> a
eval = cata alg
