


Enscript Output






> module SKI where
> import Prelude hiding (repeat, succ, pred, sum, product)

(a)

> data (Eq a, Show a) => SExpr a = Name a |
>                                  Proc a (SExpr a) |
>                                  Call (SExpr a) (SExpr a) deriving Eq

> instance (Eq a, Show a) => Show (SExpr a) where
>   show (Name n)   = show n
>   show (Proc p e) = "(lambda (" ++ show p ++ ") " ++ show e ++ ")"
>   show (Call f a) = "(" ++ show f ++ " " ++ show a ++ ")"
>

scope

> a_b = Call (Call (Proc "x" (Proc "x" (x))) (Name "a")) (Name "b")
> a_y = Call (Call (Proc "x" (Proc "y" (x))) (y)) (Name "foo")

Church booleans:

> if' = Proc "cond" (Proc "then" (Proc "else" (Call (Call (Name "cond") (Name "then")) (Name "else"))))
> true = Proc "x" (Proc "y" (x))
> false = Proc "x" (Proc "y" (y))
  
> b_this = Call (Call (Call if' true)  (Name "this")) (Name "that")
> b_that = Call (Call (Call if' false) (Name "this")) (Name "that")

(b)

> data Atom = S | K | I | Var String 
> {-machine instructions-} | IF | TRUE | FALSE
>                          | ALT | LTE | AGT | GTE | AEQ | NEQ
>                          | PLUS | MINUS | TIMES | DIV | MOD
>                          | NUM Integer deriving Eq

> instance Show Atom where
>   showsPrec _ I       = ("i" ++)
>   showsPrec _ K       = ("k" ++)
>   showsPrec _ S       = ("s" ++)
>   showsPrec _ (Var v) = (v ++)
>   showsPrec _ ALT     = ("<" ++)
>   showsPrec _ LTE     = ("<=" ++)
>   showsPrec _ AGT     = (">" ++)
>   showsPrec _ GTE     = (">=" ++)
>   showsPrec _ AEQ     = ("=" ++)
>   showsPrec _ NEQ     = ("!=" ++)
>   showsPrec _ PLUS    = ("+" ++)
>   showsPrec _ MINUS   = ("-" ++)
>   showsPrec _ DIV     = ("/" ++)
>   showsPrec _ MOD     = ("%" ++)
>   showsPrec _ TIMES   = ("*" ++)
>   showsPrec _ TRUE    = ("true" ++)
>   showsPrec _ FALSE   = ("false" ++)
>   showsPrec _ (NUM i) = shows i

> ss = Call (Name S) (Name (Var "s"))

(c)

> compile :: SExpr String -> SExpr Atom
> compile (Name n)   = Name (Var n)
> compile (Call f a) = Call (compile f) (compile a)
> compile (Proc p e) = abstract (compile e) where
>   abstract :: SExpr Atom -> SExpr Atom                  -- without Proc
>   abstract (Call f a) =                                 -- (lambda (p) (f a)) -> S f a
>     Call (Call (Name S) (abstract f)) (abstract a)      --   by rule 6 in the paper
>   abstract n@(Name (Var v)) | p == v = Name I           -- (lambda (v) v) -> I
>   abstract n@(Name _)                = Call (Name K) n  -- (lambda (p) n) -> K n

> i = compile (Proc "x" (x))
> c_b = compile a_b
> c_y = compile a_y
> c_if' = compile if'
> c_true = compile true
> c_false = compile false
> c_this = compile b_this
> c_that = compile b_that

(d)

> execute :: SExpr Atom -> SExpr Atom 
> execute prev = if prev == next then prev else execute next where
>   next = sk prev
>   sk name@(Name n)                       = name
>   sk (Call (Name I) x)                   = x
>   sk (Call (Call (Name K) x) y)          = x
>   sk (Call (Call (Call (Name S) x) y) z) = Call (Call x z) (Call y z)
>   sk (Call (Call (Name PLUS) (Name (NUM x))) (Name (NUM y))) = Name (NUM $x+y)
>   sk (Call (Call (Name MINUS) (Name (NUM x))) (Name (NUM y))) = Name (NUM $x-y)
>   sk (Call (Call (Name TIMES) (Name (NUM x))) (Name (NUM y))) = Name (NUM $x*y)
>   sk (Call (Call (Name DIV) (Name (NUM x))) (Name (NUM y))) = Name (NUM $x`div`y)
>   sk (Call (Call (Name MOD) (Name (NUM x))) (Name (NUM y))) = Name (NUM $x`mod`y)
>   sk (Call (Call (Name ALT) (Name (NUM x))) (Name (NUM y))) = boolToAtom (x < y)
>   sk (Call (Call (Name LTE) (Name (NUM x))) (Name (NUM y))) = boolToAtom (x <= y)
>   sk (Call (Call (Name AGT) (Name (NUM x))) (Name (NUM y))) = boolToAtom (x > y)
>   sk (Call (Call (Name GTE) (Name (NUM x))) (Name (NUM y))) = boolToAtom (x >= y)
>   sk (Call (Call (Name AEQ) (Name (NUM x))) (Name (NUM y))) = boolToAtom (x == y)
>   sk (Call (Call (Name NEQ) (Name (NUM x))) (Name (NUM y))) = boolToAtom (x /= y)
>   sk (Call (Call (Call (Name IF) (Name TRUE)) _then) _) = _then
>   sk (Call (Call (Call (Name IF) (Name FALSE)) _) _else) = _else
>   sk (Call x y)                          = Call (sk x) (sk y)
>   sk x                                   = error ("cannot sk: "++(show x))

> boolToAtom :: Bool -> SExpr Atom
> boolToAtom True  = Name TRUE
> boolToAtom False = Name FALSE

> a = execute (compile (Call (Proc "x" (x)) (Name "a")))
> d_ss = execute ss
> d_i = execute i
> d_b = execute c_b
> d_y = execute c_y
> d_if' = execute c_if'
> d_true = execute c_true
> d_false = execute c_false
> d_this = execute c_this
> d_that = execute c_that

(e)

shorthands:

> f = Name "f"
> g = Name "g"
> hello = Name "hello"
> m = Name "m"
> n = Name "n"
> p = Name "p"
> this = Name "this"
> that = Name "that"
> x = Name "x"
> y = Name "y"
> z = Name "z"

Church numerals:

> n0 = Proc "f" (Proc "x" x)
> n1 = Proc "f" (Proc "x" (Call f x))
> n2 = Proc "f" (Proc "x" (Call f (Call f x)))
> n3 = Proc "f" (Proc "x" (Call f (Call f (Call f x))))

Call (Call n0 (Proc "f" (Call f hello))) (Proc "x" x)
Call (Call n1 (Proc "f" (Call f hello))) (Proc "x" x)
Call (Call n2 (Proc "f" (Call f hello))) (Proc "x" x)
Call (Call n3 (Proc "f" (Call f hello))) (Proc "x" x)

iteration:

> repeat = Proc "n" (Proc "x" (Call (Call n (Proc "g" (Call g x))) (Proc "y" y)))

Call (Call repeat n2) hello

counting up and down:

> succ = Proc "n" (Proc "f" (Proc "x" (Call f (Call (Call n f) x))))
> pred = Proc "n" (Call (Call (Call n 
>                        (Proc "p" (Proc "z" (Call (Call z (Call succ (Call p true))) (Call p true)))))
>                      (Proc "z" (Call (Call z n0) n0)))
>                    false)

Call (Call repeat (Call succ n3)) hello
Call (Call repeat (Call pred n2)) hello

arithmetic:

> sum = Proc "m" (Proc "n" (Proc "f" (Proc "x" (Call (Call m f) (Call (Call n f) x)))))
> product = Proc "m" (Proc "n" (Proc "f" (Call m (Call n f))))
  
Call (Call repeat (Call (Call sum n2) n3)) hello
Call (Call repeat (Call (Call product n2) n3)) hello

predicate:

> isZero = Proc "n" (Call (Call n (Proc "x" false)) true)

Call (Call (Call if' (Call isZero n0)) this) that
Call (Call (Call if' (Call isZero n1)) this) that

recursion:

> r = Proc "f" (Proc "n" (Call (Call (Call if' (Call isZero n)) n1) (Call (Call product n) (Call f (Call pred n)))))
> ycomb = Proc "y" (Call (Proc "x" (Call y (Call x x))) (Proc "x" (Call y (Call x x))))
> factorial = Call ycomb r

Call (Call repeat (Call factorial (Call (Call product n2) n2))) hello

Generated by GNU enscript 1.6.3.


