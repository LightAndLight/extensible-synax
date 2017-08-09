# Programmable Syntax
What if a programming language's parser was metaprogrammable?

Consider a lambda-calculus based language with quasi-quotation, strings, ints, and generalized algebraic
datatypes. Naively implemented in Haskell, the abstract syntax tree, let's call it `ex`, might appear as
follows:

```haskell
-- AST.hs

data AST
  = Var String
  | Abs String AST
  | App AST AST
  | DataCon String
  | LitString String
  | LitInt Int
  | Quote AST
  deriving (Eq, Show)
```

To achieve homoiconicity, there must be an `ex` ADT that exactly mirrors the Haskell AST, and then
a partial mapping from the Haskell representation of the `ex` ADT directly to Haskell. Here's what
that would look like:

```haskell
-- AST.ex

data AST
  = Var String
  | Abs String AST
  | App AST AST
  | DataCon String
  | LitString String
  | LitInt Int
  | Quote AST
```

```haskell
-- AST.hs

reifyAST :: AST -> AST
reifyAST ast =
  case ast of
    App (DataCon "Var") (LitString a) -> Var a
    App (App (DataCon "Abs") (LitString a)) b -> Abs a (reifyAST b)
    App (App (DataCon "App") a) b -> App (reifyAST a) (reifyAST b)
    App (DataCon "DataCon") (LitString a) -> DataCon a
    App (DataCon "LitString") (LitString a) -> LitString a
    App (DataCon "LitInt") (LitInt a) -> LitInt a
    App (DataCon "Quote") a -> a
    _ -> error "internal error: invalid argument to reifyAST: " ++ show ast
```

Now that we have defined `ex` language and given the compiler a way to introspect it,
we can explore the effects of reifying the parser. First, we define the type of parser
scripts in `ex`:

```haskell
--- Syntax.ex

data Syntax : Type -> Type where
  Pure : a -> Syntax a
  Bind : Syntax a -> (a -> Syntax b) -> Syntax b
  Discard : Syntax a -> Syntax b -> Syntax b
  Satisfy : (Char -> Bool) -> Syntax Char
  String : String -> Syntax String
  -- et cetera
```

The constructors correspond to the parser combinators that will be used in the host language.

Next we introduce a pragma that will cause the compiler to lift a syntax definition during
parsing: `%syntax`. `%syntax` takes an argument of type `Syntax AST`. When encountered, its
argument will transformed into a Haskell parser script, and added to the list of productions
to be used throughout the rest of the file. We will also introduce syntax for quoting (`'`), for
convenience.

Example:
```
-- Example.ex

data Unit = Unit

syn : Syntax AST
syn = Discard (String "unit") (Pure 'Unit)

%syntax syn

test : Unit
test = unit
```

Herein lies the first potential pitfall: how does this program behave when using separate type
and term level languages? Is `'Unit` referring the the type constructor or data constructor?
We could limit syntax extension to terms to remove ambiguity. This seems unduly restrictive,
and it might be better to unify type and term level languages with dependent types. Assuming
dependent types, the example becomes:

```
-- Example.ex

data Unit = MkUnit

syn : Syntax AST
syn = Discard (String "unit") (Pure 'MkUnit)

%syntax syn

test : Unit
test = unit
```

Next, there needs to be a mapping from the `ex` representation from `Syntax` specifications to
Haskell values. This function will assume that the syntax specification will produce a reifiable AST,
which is why the argument to `%syntax` must produce an `AST`:

```haskell
--- Syntax.hs

reifySyntax :: AST -> Parser AST
reifySyntax ast =
  case ast of
    App (DataCon "Pure") a -> pure (reifyAST a)
    App (App (DataCon "Bind) a) f -> reifySyntax a >>= reifySyntax . eval . App f . Quote
    App (App (DataCon "Discard") a) b -> reifySyntax a >> reifySyntax b
    App (DataCon "Satisfy") pred -> satisfy ((== DataCon "True") . eval . App pred . LitChar)
    App (DataCon "String") (LitString str) -> string str
```
