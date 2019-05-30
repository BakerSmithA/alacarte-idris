module Fix

public export
data Fix : (f : Type -> Type) -> Type where
    In : f (Fix f) -> Fix f

export
inop : Fix f -> f (Fix f)
inop (In x) = x

export
cata : Functor f => (f a -> a) -> Fix f -> a
cata alg = alg . map (cata alg) . inop
