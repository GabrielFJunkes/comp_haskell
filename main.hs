{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import System.IO

type Id = String
data Tipo = TDouble | TInt | TString | TVoid deriving Show --
data TCons = CDouble Double | CInt Integer deriving Show
data Expr = Expr :+: Expr | Expr :-: Expr | Expr :*: Expr | Expr :/: Expr | Neg Expr | Const TCons | IdVar String | Chamada Id [Expr] | Lit String deriving Show
data ExprR = Expr :==: Expr | Expr :/=: Expr | Expr :<: Expr | Expr :>: Expr | Expr :<=: Expr | Expr :>=: Expr deriving Show
data ExprL = ExprL :&: ExprL | ExprL :|: ExprL | Not ExprL | Rel ExprR deriving Show
data Var = Id :#: Tipo deriving Show --
data Funcao = Id :->: ([Var], Tipo) deriving Show  --
data Programa = Prog [Funcao] [(Id, [Var], Bloco)] [Var] Bloco deriving Show --
type Bloco = [Comando]
data Comando = If ExprL Bloco Bloco | While ExprL Bloco | Atrib Id Expr | Leitura Id | Imp Expr | Ret (Maybe Expr) | Proc Id [Expr] deriving Show

exprR = do{
        e1 <- expr;
        o <- opR;
        e2 <- expr;
        return (Rel (o e1 e2))
}

opR =   do { reservedOp "=="; return (:==:)}
    <|> do { reservedOp "/="; return (:/=:)}
    <|> do { reservedOp "<="; return (:<=:)}
    <|> do { reservedOp ">="; return (:>=:)}
    <|> do { reservedOp "<"; return (:<:)}
    <|> do { reservedOp ">"; return (:>:)}

comando = do {
        reserved "return";
        e<-expr;
        semi;
        return (Ret (Just e));
    }
    <|> do {
        reserved "while";
        l <- parens exprL;
        b<-bloco;
        return (While l b);
    }

listaCmd = do {
        c <- comando;
        cs <- listaCmd;
        return (c : cs);
    }
    <|> return [];

bloco = do {
        symbol "{";
        cs <- listaCmd;
        symbol "}";
        return cs;
    }

-- data Var = Id :#: Tipo deriving Show

defineTipo =   do { reservedOp "int"; return (TInt)}
    <|> do { reservedOp "double"; return (TDouble)}
    <|> do { reservedOp "string"; return (TString)}
    <|> do { reservedOp "void"; return (TVoid)}

var = do {
    t <- defineTipo;
    n <- identifier;
    return (n :#: t);
}

-- data Funcao = Id :->: ([Var], Tipo) deriving Show
funcao = do {
    t <- defineTipo;
    n <- identifier;
    symbol "(";
    lv <- commaSep var;
    symbol ")";
    return (n :->: (lv, t))
}

-- data Programa = Prog [Funcao] [(Id, [Var], Bloco)] [Var] Bloco deriving Show




lingDef = emptyDef {
        T.commentStart = "{-"
    ,   T.commentEnd = "-}"
    ,   T.commentLine = "--"
    ,   T.identStart = letter <|> char '_'
    ,   T.identLetter = alphaNum <|> char '_'
    ,   T.reservedOpNames = ["+", "-", "/", "*", "&&", "||", "!", "<", ">", "<=", ">=", "==", "/="]
    ,   T.reservedNames = ["while", "return"]
}

lexico = T.makeTokenParser lingDef

natural = T.natural lexico
symbol = T.symbol lexico
parens = T.parens lexico
reservedOp = T.reservedOp lexico
identifier = T.identifier lexico
reserved = T.reserved lexico
semi = T.semi lexico
comma = T.comma lexico
commaSep = T.commaSep lexico

tabela = [
        [prefix "-" Neg],
        [binario "*" (:*:) AssocLeft, binario "/" (:/:) AssocLeft ],
        [binario "+" (:*:) AssocLeft, binario "-" (:-:) AssocLeft ]
    ]

tabelaL = [
        [prefix "!" Not],
        [binario "&&" (:&:) AssocLeft ],
        [binario "||" (:|:) AssocLeft ]
    ]

binario name fun assoc = Infix (do{reservedOp name; return fun }) assoc
prefix name fun = Prefix (do{reservedOp name; return fun })

exprL = buildExpressionParser tabelaL exprR
    <?> "expression"

expr = buildExpressionParser tabela fator
    <?> "expression"

fator = parens expr
    <|> do{n <- natural; return (Const (CInt n))}
    <|> do{n <- identifier; return (IdVar n)}
    <?> "simple expression"

partida :: Parsec String u Funcao
partida = do {e <- funcao; eof; return e}

parserE e = runParser partida [] "Expressoes" e

parserExpr s = case parserE s of
    Left er -> print er
    Right v -> (print v)

main = do {putStr "Expressão:";
    hFlush stdout;
    e <- getLine;
    parserExpr e}