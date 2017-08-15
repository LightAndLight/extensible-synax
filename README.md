# Programmable Syntax

What if a programming language's parser was metaprogrammable?

What follows is my stream-of-consciousness investigation into this idea.

Consider a lambda-calculus based language with quasi-quotation, strings, ints, and generalized algebraic
datatypes. Naively implemented in Haskell, the abstract syntax tree, let's call it `ex`, might appear as
follows:

```haskell
-- Expr.hs

data Expr
  = Var String
  | Abs String Expr
  | App Expr Expr
  | Ctor String
  | LitString String
  | LitInt Int
  | Quote Expr
  deriving (Eq, Show)
```

To achieve homoiconicity, there must be an `ex` ADT that exactly mirrors the Haskell AST, and then
a partial mapping from the Haskell representation of the `ex` ADT directly to Haskell. Here's what
that would look like:

```haskell
-- Expr.ex

data Expr
  = Var String
  | Abs String Expr
  | App Expr Expr
  | Ctor String
  | LitString String
  | LitInt Int
  | Quote Expr
```

```haskell
-- Expr.hs

reifyExpr :: Expr -> Expr
reifyExpr ast =
  case ast of
    App (Ctor "Var") (LitString a) -> Var a
    App (App (Ctor "Abs") (LitString a)) b -> Abs a (reifyExpr b)
    App (App (Ctor "App") a) b -> App (reifyExpr a) (reifyExpr b)
    App (Ctor "Ctor") (LitString a) -> Ctor a
    App (Ctor "LitString") (LitString a) -> LitString a
    App (Ctor "LitInt") (LitInt a) -> LitInt a
    App (Ctor "Quote") a -> a
    _ -> error "internal error: invalid argument to reifyExpr: " ++ show ast
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
parsing: `%%syntax`. `%%syntax` takes an argument of type `Syntax Expr`. When encountered, its
argument will transformed into a Haskell parser script, and added to the list of productions
to be used throughout the rest of the file. We will also introduce syntax for quoting (`'`), for
convenience.

Example:
```
-- Example.ex

data Unit = Unit

syn : Syntax Expr
syn = Discard (String "unit") (Pure 'Unit)

%%syntax syn

test : Unit
test = unit
```

Herein lies the first potential pitfall: how does this program behave when using separate type
and term level languages? Is `'Unit` referring the the type constructor or data constructor?
We could limit syntax extension to terms to remove ambiguity. This seems unduly restrictive,
and it might be better to unify type and term level languages with dependent types. Assuming
dependent types, the example becomes:

```idris
-- Example.ex

data Unit = MkUnit

syn : Syntax Expr
syn = Discard (String "unit") (Pure 'MkUnit)

%syntax syn

test : Unit
test = unit
```

Next, there needs to be a mapping from the `ex` representation from `Syntax` specifications to
Haskell values. This function will assume that the syntax specification will produce a reifiable Expr,
which is why the argument to `%syntax` must produce an `Expr`:

```haskell
--- Syntax.hs

reifySyntax :: Expr -> Parser Expr
reifySyntax ast =
  case ast of
    App (Ctor "Pure") a -> pure (reifyExpr a)
    App (App (Ctor "Bind") a) f -> reifySyntax a >>= reifySyntax . eval . App f . quote
    App (App (Ctor "Discard") a) b -> reifySyntax a >> reifySyntax b
    App (Ctor "Satisfy") pred -> satisfy ((== Ctor "True") . eval . App pred . LitChar)
    App (Ctor "String") (LitString str) -> string str
  where
    -- Transforms haskell AST into `ex` representation of haskell AST
    quote :: Expr -> Expr
    ...
```

This presentation allows arbitrary code to be executed during the parse phase, so efforts must
be made to check the totality of the involved code. Since this will likely be in a dependently
typed language, this will likely be implemented anyway.

The parsing and typechecking phases are now coupled. During parsing, definitions should be typechecked
and added to the context immediately, because they could be required to form the next syntax extension.

Let's now explore how the compiler can dynamically add new syntax rules. The simplest approach is to
maintain a list of rules to which new rules are prepended. Then when an expression is to be parsed,
the first rule that applied can be selected:

```haskell
--- Compiler.hs

syntaxRule
  :: ( MonadState [Parser Expr] m
     , MonadParser m
     , MonadTypecheck m
     )
  => m ()
syntaxRule = do
  token "%syntax"
  ast <- gets choice
  ast `hasType` App (Ctor "Syntax") (Ctor "Expr")
  modify (reifySyntax ast :)
```

Unfortunately, this does not accurately model how grammar productions are related. A system based on
the above idea assumes that every production equal precedence to those previously defined, and will
attempt to parse the newest production first before the later ones. The linked-list approach is really
a specialization of the desired approach: a directed graph.

Similarly, we need a generalization of the `choice` combinator from lists to directed graphs. Let's analyze
some examples to consider how this may work:

```
a -->--v
       |
b -->--|
       |-->-- root
c -->--|
       |
d -->--^


root = a <|> b <|> c <|> d
root = choice [a, b, c, d]
```

```
# n -->-- m means m has higher precedence than n #

a -->-- b -->--v
|              |
> -->-- c -->--v
        |      |
d -->---^      |-->-- root
        |      |
e -->---^      |
        |      |
f -->---^--->--^

root = (b <|> a) <|> (c <|> (a <|> d <|> e <|> f)) <|> f 
root =
  let
    aNode = Node a []
    dNode = Node d []
    eNode = Node e []
    fNode = Node f []
  in 
  grammar [Node b [aNode], Node c [aNode, dNode, eNode, fNode], Node f []]
  where
    grammar [] = empty
    grammar (Node val children:nodes) = (val <|> grammar children) <|> grammar nodes
```

If syntax rules could reference other syntax rules, then the graph can be constructed and
updated, and used to correctly parse all the productions with respect to each other.

Let's introduce extra syntax to give syntax rules names: `%%syntax [expr|decl|module] <name> = <val>`.
`<name>` will have type `Syntax [Expr|Decl|Module]`, but is only in scope within subsequent syntax
rule definitions. It seems to be a desirable property to prevent the contruction of ambiguous grammars
in this system. Is it possible to determine whether or not a grammar is ambiguous given a directed graph
representation? Additionally, it might be important to determine if the grammar is LL, since the implementation
uses parser combinators.

Cyclicity is not a concern, since grammars can be simultaneously recursive and unambiguous i.e.
`term ::= left right; left ::= 'value'; right ::= '+' term right | epsilon`. Therefore it should be permitted
to have self- and mutally- recursive syntax rules. To support this, it may be helpful to add 'syntax blocks', to
denote mutually recursive sets of syntax rules:
`%%syntax [expr|decl|module]; a_1 = ... b_1; b_1 = ... a_1; %%syntax`
Apparently determining
the ambiguity of a context free grammar is undecidable, but `ll(k)` and `lr(k)` grammars are unambiguous,
so maybe the burden can be shifted to deciding if the grammar is in that class. It is also worth considering
restricting the parser combinators to permit only this class of grammars. This may require its own library. The
best way to do this would be to build the parse table and detect any conflicts, and if there are no conflicts
then build a parser specification in terms of `parsers` typeclasses. Parser combinators work best with `ll`
grammars, but there is an isomorphism between `ll` and `lr` grammars, so in theory we could validate that
a given grammar is `lr`, then translate it to parser combinators anyway.
