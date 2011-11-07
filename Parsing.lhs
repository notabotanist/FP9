> module Parsing where
> import Char -- isDigit and other predicates
> import Monad -- MonadPlus

patterned after Hutton's "Programming in Haskell"

a ParserFunction accepts a string and produces a list
which is empty on failure or contains a tuple with a result
and the rest of the string on success.

> type ParserFunction a = String -> [(a, String)]

success value
is a ParserFunction which always succeeds with the result value.

> success :: a -> ParserFunction a
> success value = \input -> [(value, input)]

failure
is a ParserFunction which always fails.

> failure :: ParserFunction a
> failure = \_ -> []

item
is a ParserFunction which fails if the input string is empty
and succeeds with the first input character otherwise.

> item :: ParserFunction Char
> item = \input -> case input of
>                    []     -> []
>                    (x:xs) -> [(x, xs)]

eof
is a ParserFunction which fails if the input string is not empty
and succeeds with the empty tuple otherwise.

> eof :: ParserFunction ()
> eof = \input -> case input of
>                   [] -> [((), [])]
>                   _  -> []

examples:
  success 1 "abc"
  failure "abc"
  item ""
  item "abc"
  eof ""
  eof "abc"

a Parser contains a ParserFunction.

> data Parser a = Parser (ParserFunction a)

Parsers can parse, i.e., parse accepts a Parsers instance and
returns the ParserFunction which the instance contains.
In fact, parse accepts a Parsers instance and an input string
and produces a list of tuples.

> class Parsers p
>   where parse :: p a -> ParserFunction a
> --            :: p a -> String -> [(a, String)]

a Parser belongs to the class of Parsers because we can implement parse
by applying the contained ParserFunction to an input string.

> instance Parsers Parser where
>    parse (Parser p) = p
> -- parse (Parser p) input = p input

examples:
  parse (Parser $ success 1) "abc"
  parse (Parser failure) "abc"
  parse (Parser item) ""
  parse (Parser item) "abc"

sequential execution: p1 `bind` p2
accepts a Parser and a function which must return a Parser
and returns a ParserFunction which has the effect of
applying two parsers, one after another, to return the combined result.

> bind :: Parser a -> (a -> Parser b) -> ParserFunction b
> p1 `bind` p2 = \input -> case parse p1 input of
>                            []            -> []
>                            [(v, output)] -> parse (p2 v) output

example: parse p13 string
picks the first and third character from a string.
  parse p13 "ab"
  parse p13 "abcdef"

> p13 :: Parser (Char, Char)
> p13 =       (Parser item)            `andThen`
>       \a -> (Parser item)            `andThen`
>       \_ -> (Parser item)            `andThen`
>       \c -> (Parser $ success (a,c))
>   where
>     a `andThen` b = Parser (a `bind` b)

a Parser belongs to the class of Monads because we can implement
the required operations.

> instance Monad Parser where
>   return value = Parser (success value)
>   fail _       = Parser (failure)
>   a >>= b      = Parser (a `bind` b)

example: parse mp13 string
picks the first and third character from a string.
This uses the much more intuitive 'do' notation for values
of instances of Monad which completely hides failure and
the maintaining of the rest of the input string ("state").
  parse mp13 "ab"
  parse mp13 "abcdef"

> --mp13 :: Parser (Char, Char)
> mp13 = do a <- Parser item
>           Parser item
>           c <- Parser item
>           return [a,c]

sat p
a Parser for single characters which satisfy the predicate p.

> sat :: (Char -> Bool) -> Parser Char
> sat p = do x <- Parser item
>            if p x then return x else fail "parse error"

examples: Parser for single digit, etc.
  parse digit "123"
  parse digit "abc"
  parse lower "abc"
  parse lower "ABC"
  parse upper "ABC"
  parse upper "abc"
  parse letter "abc"
  parse letter "ABC"
  parse letter "123"
  parse alphanum "abc"
  parse alphanum "ABC"
  parse alphanum "123"
  parse alphanum " "
  parse (char 'a') "abc"
  parse (char 'c') "abc"
  parse (string "xs") "xs"
  parse (string "xs") "xylophon"

> digit :: Parser Char
> digit = sat isDigit

> lower :: Parser Char
> lower = sat isLower

> upper :: Parser Char
> upper = sat isUpper

> letter :: Parser Char
> letter = sat isAlpha

> alphanum :: Parser Char
> alphanum = sat isAlphaNum

> char :: Char -> Parser Char
> char x = sat (== x)

> string :: String -> Parser String
> string [] = return []
> string (x:xs) = do char x
>                    string xs
>                    return (x:xs)

decision: p1 `alt` p2
returns a Parser which applies p1 to input
and if this fails it tries to apply p2.
  parse (Parser $ Parser item `alt` return 'd') "abc"
  parse (Parser $ fail "" `alt` return 'd') "abc"
  parse (Parser $ fail "" `alt` fail "") "abc"

> alt :: Parser a -> Parser a -> ParserFunction a
> p1 `alt` p2 = \input -> case parse p1 input of
>                           []            -> parse p2 input
>                           [(v, output)] -> [(v, output)]

a Parser belongs to the class MonadPlus because we can implement
the required operations.

> instance MonadPlus Parser where
>   mzero       = Parser failure
>   a `mplus` b = Parser (a `alt` b)

examples
Note that mzero fails (and usually needs to be typed explicitly)
and that mplus should be read as "or else".
  parse (Parser item `mplus` return 'd') "abc"
  parse ((mzero :: Parser Char) `mplus` return 'd') "abc"
  parse ((mzero :: Parser ()) `mplus` mzero) "abc"

iteration: many p
           some p
a Parser which applies a Parser zero or more times (many)
or one or more times (some) and returns a list with the results.

> many :: Parser a -> Parser [a]
> many p = some p `mplus` return []

> some :: Parser a -> Parser [a]
> some p = do value <- p
>             values <- many p
>             return (value:values)

examples
  parse (many digit) "123abc"
  parse (many digit) "abc"
  parse (some digit) "abc"

examples: Parser for identifier (lower-case followed by alphanums),
natural number, and white space (which is effectively discarded).
  parse ident "abc def"
  parse num "123abc"
  parse space "   abc"

> ident :: Parser String
> ident = do value <- lower
>            values <- many alphanum
>            return (value:values)

> num :: Parser Int
> num = do digits <- some digit
>          return (read digits)

> space :: Parser ()
> space = do many (sat isSpace)
>            return ()

token p
a Parser which ignores white space surrounding what p finds.

> token :: Parser a -> Parser a
> token p = do space
>              value <- p
>              space
>              return value

examples: Parser for identifier (lower-case followed by alphanums),
natural number, and specific text, all surrounded by white space.
  parse identifier " foo bar "
  parse identifier " 123 bar "
  parse number " 123 bar "
  parse number " foo bar "
  parse (symbol "foo") " foo bar "
  parse (symbol "foo") " 123 bar "

> identifier :: Parser String
> identifier = token ident

> number :: Parser Int
> number = token num

> symbol :: String -> Parser String
> symbol word = token (string word)

example: parser for list of numbers, comma-separated, white space ignored.
  parse numbers " [1, 2 , 3 ] "
  
> numbers :: Parser [Int]
> numbers = do symbol "["
>              n <- number
>              ns <- many (do symbol ","
>                             number)
>              symbol "]"
>              return (n:ns)

numbers: '[' number (',' number)* ']';

enumbers: '[' ( number ( ',' number)* )? ']';

> opt p = do value <- p
>            return [value]
>         `mplus`
>            return []

> enumbers = do symbol "["
>               l <- opt (do n <- number
>                            ns <- many (do symbol ","
>                                           number)
>                            return (n:ns))
>               symbol "]"
>               return l

Generated by GNU enscript 1.6.3.
