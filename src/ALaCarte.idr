module ALaCarte

import Fix

%access public export

data Sig : (fs : List (Type -> Type)) -> (a : Type) -> Type where
    Here  : f a -> Sig (f :: fs) a
    There : Sig fs a -> Sig (f :: fs) a

data Elem : (f : Type -> Type) -> (fs : List (Type -> Type)) -> Type where
    H : Elem f (f :: fs)
    T : Elem f ys -> Elem f (y :: ys)

inj : {auto prf : Elem f fs} -> f a -> Sig fs a
inj {prf=H}   x = Here x
inj {prf=T t} x = There (inj {prf=t} x)

inject : {auto prf : Elem f fs} -> f (Fix (Sig fs)) -> Fix (Sig fs)
inject = In . inj

Functor (Sig []) where
    map _ (Here _) impossible
    map _ (There _) impossible

(Functor f, Functor (Sig fs)) => Functor (Sig (f :: fs)) where
    map func (Here x) = Here (map func x)
    map func (There t) = There (map func t)

interface Alg (f : Type -> Type) (a : Type) where
    alg : f a -> a

Alg (Sig []) a where
    alg (Here _) impossible
    alg (There _) impossible

(Alg f a, Alg (Sig fs) a) => Alg (Sig (f :: fs)) a where
    alg (Here x) = alg x
    alg (There x) = alg x

eval : (Functor f, Alg f a) => Fix f -> a
eval = cata alg
