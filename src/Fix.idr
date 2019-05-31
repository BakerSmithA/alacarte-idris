module Fix

%access public export

data Fix : (f : Type -> Type) -> Type where
    In : f (Fix f) -> Fix f

Show (f (Fix f)) => Show (Fix f) where
    show x = "In " ++ show x

inop : Fix f -> f (Fix f)
inop (In x) = x

cata : Functor f => (f a -> a) -> Fix f -> a
cata alg = alg . map (cata alg) . inop
