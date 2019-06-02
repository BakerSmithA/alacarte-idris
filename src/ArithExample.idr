module ArithExample

import Fix
import ALaCarte

%access public export

-- DSL for arithmetic expressions

data Val k = V Int
data Add k = A k k
data Mul k = M k k

Expr : Type
Expr = Fix (Sig [Val, Add, Mul])

Functor Val where
    map func (V x) = V x

Functor Add where
    map func (A x y) = A (func x) (func y)

Functor Mul where
    map func (M x y) = M (func x) (func y)

-- Smart constructors

val : {auto prf : Elem Val fs} -> Int -> Fix (Sig fs)
val x = inject (V x)

(+) : {auto prf : Elem Add fs} -> Fix (Sig fs) -> Fix (Sig fs) -> Fix (Sig fs)
x + y = inject (A x y)

(*) : {auto prf : Elem Mul fs} -> Fix (Sig fs) -> Fix (Sig fs) -> Fix (Sig fs)
x * y = inject (M x y)

-- Evaluation

Alg Val Int where
    alg (V x) = x

Alg Add Int where
    alg (A x y) = x + y

Alg Mul Int where
    alg (M x y) = x * y

calc : Expr -> Int
calc = eval

-- Pretty Printing

Alg Val String where
    alg (V x) = show x

Alg Add String where
    alg (A x y) = "(" ++ x ++ " + " ++ y ++ ")"

Alg Mul String where
    alg (M x y) = "(" ++ x ++ " * " ++ y ++ ")"

pretty : Expr -> String
pretty = eval

-- Examples

ex1 : Expr
ex1 = (val 1 + val 2) * val 3

runEx : Expr -> IO ()
runEx e = do
    putStrLn (pretty e)
    putStrLn (show (calc e))
