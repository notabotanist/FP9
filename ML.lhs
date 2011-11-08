This is a modified parser for the mini-language (based on the Parsing module
from the class notes) which either fails or returns an SExpr Atom of the parsed
expression.

> module ML where
> import Prelude hiding (div, id, mod, repeat, succ, pred, sum, product)
> import Monad (mplus)
> import Parsing
> import System (getArgs)
> import SKI hiding (true, false)

:run test path
convenience function to parse the contents of a file.

> test = do
>   args <- getArgs
>   contents <- readFile (head args)
>   putStrLn $ show (parse prog contents)

the grammar.

> prog =   do e <- expr                -- prog: expr eof
>             Parser eof
>             return e

> expr =   do s <- sums                -- expr: sums (relop sums)?
>             c <- (gt `mplus` ge `mplus` lt `mplus` le `mplus` eq `mplus` ne)
>             return (Call c s)
>          `mplus`
>          do sums

> gt =     do symbol ">"          -- relop: '>' sums
>             s <- sums
>             return (Call (Name AGT) s)

> ge =     do symbol ">="         -- relop: '>=' sums
>             s <- sums
>             return (Call (Name GTE) s)

> lt =     do symbol "<"          -- relop: '<' sums
>             s <- sums
>             return (Call (Name ALT) s)

> le =     do symbol "<="         -- relop: '<=' sums
>             s <- sums
>             return (Call (Name LTE) s)

> eq =     do symbol "="          -- relop: '=' sums
>             s <- sums
>             return (Call (Name AEQ) s)

> ne =     do symbol "!="         -- relop: '!=' sums
>             s <- sums
>             return (Call (Name NEQ) s)

> sums =   do p <- prods              -- sums: prods (addop prods)*
>             s <- many (add `mplus` sub)
>             if s == []
>               then
>                 return p
>               else
>                 return (doCalls (reverse (p:s)))
>                   where
>                     doCalls [x] = x
>                     doCalls (x:xs) = (Call x (doCalls xs))

> add =    do symbol "+"          -- addop: '+' prods
>             p <- prods
>             return (Call (Name PLUS) p)

> sub =    do symbol "-"          -- addop: '-' prods
>             p <- prods
>             return (Call (Name MINUS) p)

> prods =  do t <- term                -- prods: term (mulop term)*
>             s <- many (mul `mplus` div `mplus` mod)
>             if s == []
>               then
>                 return t
>               else
>                 return (doCalls (reverse (t:s)))
>                   where
>                     doCalls [x] = x
>                     doCalls (x:xs) = (Call x (doCalls xs))

> mul =    do symbol "*"          -- mulop: '*' term
>             t <- term
>             return (Call (Name TIMES) t)

> div =    do symbol "/"          -- mulop: '/' term
>             t <- term
>             return (Call (Name DIV) t)

> mod =    do symbol "%"          -- mulop: '%' term
>             t <- term
>             return (Call (Name MOD) t) 

> term =   lEt
>          --`mplus` letrec       (letrec currently unimplemented)
>          `mplus` lambda
>          `mplus` cond
>          `mplus` parens
>          `mplus` call
>          `mplus` true
>          `mplus` false
>          `mplus` value
>          `mplus` id

> lEt =    do symbol "let"        -- let: 'let' (id '=' expr)+ 'in' expr
>             binds <- some (do i <- idAtom
>                               symbol "="
>                               e <- expr
>                               return (i,e))
>             symbol "in"
>             ex <- expr
>             return (applyBinds binds ex)
>               where
>                 applyBinds [b] ex = (Call (Proc (fst b) ex) (snd b))
>                 applyBinds (b:bs) ex = (Call (Proc (fst b) (applyBinds bs ex)) (snd b))

> lambda = do symbol "lambda"     -- lambda: 'lambda' id '.' expr
>             i <- idAtom
>             symbol "."
>             e <- expr
>             return (Proc i e)

> cond =   do symbol "cond"       -- cond: 'cond' (expr expr)+ 'end'
>             exprs <- some (do e1 <- expr
>                               e2 <- expr
>                               return (e1,e2))
>             symbol "end"
>             return (applyPairs exprs)
>               where
>                 applyPairs [(e1,e2)] = (Call (Call (Call (Name IF) e1) e2) (Name FALSE))
>                 applyPairs ((e1,e2):es) = (Call (Call (Call (Name IF) e1) e2) (applyPairs es))

> parens = do symbol "("          -- parens: '(' expr ')'
>             e <- expr
>             symbol ")"
>             return e

> call =   do symbol "("          -- call: '(' expr expr+ ')'
>             e <- expr
>             es <- some expr
>             symbol ")"
>             return (applyCalls e es)
>               where
>                 applyCalls e [e0] = (Call e e0)
>                 applyCalls e (x:xs) = (Call (applyCalls e xs) x)

> true =   do symbol "true"       -- true: 'true'
>             return (Name TRUE)

> false =  do symbol "false"      -- false: 'false'
>             return (Name FALSE)

> value =  do n <- number         -- value: number
>             return (Name (NUM n))

> id =     do i <- idAtom
>             return (Name i)

> idAtom = do i <- identifier     -- name: identifier
>             if i `notElem` reserved then return (Var i) else fail "" where

>   reserved = [ "cond", "end",   -- but not reserved word
>                "false", "in", "lambda", "let", "letrec", "true" ]

