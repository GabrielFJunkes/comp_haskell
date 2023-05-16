{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import System.IO

type Id = String
data Tipo = TDouble | TInt | TString | TVoid deriving Show --
data TCons = CDouble Double | CInt Integer | CString String deriving Show
data Expr = Expr :+: Expr | Expr :-: Expr | Expr :*: Expr | Expr :/: Expr | Neg Expr | Const TCons | IdVar String | Chamada Id [Expr] | Lit String deriving Show
data ExprR = Expr :==: Expr | Expr :/=: Expr | Expr :<: Expr | Expr :>: Expr | Expr :<=: Expr | Expr :>=: Expr deriving Show
data ExprL = ExprL :&: ExprL | ExprL :|: ExprL | Not ExprL | Rel ExprR deriving Show
data Var = Id :#: Tipo deriving Show --
data Funcao = Id :->: ([Var], Tipo) deriving Show  --
data Programa = Prog [Funcao] [(Id, [Var], Bloco)] [Var] Bloco deriving Show --
type Bloco = [Comando]
data Comando = If ExprL Bloco Bloco | While ExprL Bloco | Atrib Id Expr | Leitura Id | Imp Expr | Ret (Maybe Expr) | Proc Id [Expr] deriving Show

exprR = do {
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
        reserved "if";
        l <- parens exprL;
        b1<-bloco;
        b2<-senao;
        return (If l b1 b2);
    }
    <|> do {
        reserved "while";
        l <- parens exprL;
        b<-bloco;
        return (While l b);
    }
    <|> try (do {
         n<-identifier;
         e<-parens (commaSep expr);
         semi;
         return (Proc n e);
     })
    <|> do {
        n <- identifier;
        reservedOp "=";
        e<-expr;
        semi;
        return (Atrib n e);
    }
    <|> do {
        reserved "print";
        e<- parens expr;
        semi;
        return (Imp e);
    }
    <|> do {
        reserved "read";
        x<- parens identifier;
        semi;
        return (Leitura x);
    }

listaCmd = do {
        c <- comando;
        cs <- listaCmd;
        return (c : cs);
    }
    <|> return [];

bloco = do {
        braces listaCmd;
    }

senao = do {
           reserved "else";
           bloco;
        }
        <|> return [];

-- data Var = Id :#: Tipo deriving Show

defineTipo =   do { reservedOp "int"; return TInt}
    <|> do { reservedOp "double"; return TDouble}
    <|> do { reservedOp "string"; return TString}
    <|> do { reservedOp "void"; return TVoid}

var = do {
    t <- defineTipo;
    n <- identifier;
    return (n :#: t);
}

-- data Funcao = Id :->: ([Var], Tipo) deriving Show
funcao = do {
    t <- defineTipo;
    n <- identifier;
    lv <- parens (commaSep var);
    return (n :->: (lv, t))
}

funcaoEBloco = do {
            f <- funcao;
            b <- bloco;
            lfb <- funcaoEBloco;
            return ((f,b) : lfb);
        }
        <|> return [];


funcaoId (id :->: _) = id
funcaoVar (_ :->: (vars, _)) = vars

retornaFuncao [] = []
retornaFuncao ((f, _):t) = f : retornaFuncao t

retornaBloco [] = []
retornaBloco ((_, b):t) = b : retornaBloco t

retornaIdVarBloco :: [(Funcao, Bloco)] -> [(Id, [Var], Bloco)]
retornaIdVarBloco [] = []
retornaIdVarBloco ((f,b):t) = (funcaoId f, funcaoVar f, b) : retornaIdVarBloco t

-- data Programa = Prog [Funcao] [(Id, [Var], Bloco)] [Var] Bloco deriving Show
programa = do
            lfb <- funcaoEBloco;
            let lf = retornaFuncao lfb;
            let idVarBloco = retornaIdVarBloco lfb;
            b <- bloco;
            return (Prog lf idVarBloco [] b);

lingDef = emptyDef {
        T.commentStart = "{-"
    ,   T.commentEnd = "-}"
    ,   T.commentLine = "--"
    ,   T.identStart = letter <|> char '_'
    ,   T.identLetter = alphaNum <|> char '_'
    ,   T.reservedOpNames = ["+", "-", "/", "*", "&&", "||", "!", "<", ">", "<=", ">=", "==", "/=", "="]
    ,   T.reservedNames = ["while", "return", "if", "else", "print", "read"]
}

lexico = T.makeTokenParser lingDef

natural = T.natural lexico
symbol = T.symbol lexico
parens = T.parens lexico
reservedOp = T.reservedOp lexico
identifier = T.identifier lexico
reserved = T.reserved lexico
semi = T.semi lexico
commaSep = T.commaSep lexico
float = T.float lexico
stringLiteral = T.stringLiteral lexico
braces = T.braces lexico

tabela = [
        [prefix "-" Neg],
        [binario "*" (:*:) AssocLeft, binario "/" (:/:) AssocLeft ],
        [binario "+" (:+:) AssocLeft, binario "-" (:-:) AssocLeft ]
    ]

tabelaL = [
        [prefix "!" Not],
        [binario "&&" (:&:) AssocLeft ],
        [binario "||" (:|:) AssocLeft ]
    ]

binario name fun assoc = Infix (do {reservedOp name; return fun }) assoc
prefix name fun = Prefix (do {reservedOp name; return fun })

exprL = buildExpressionParser tabelaL exprR
    <?> "expression"

expr = buildExpressionParser tabela fator
    <?> "expression"

fator = parens expr
    <|> try (do {
         n <- identifier;
         le<- parens (commaSep expr);
         return (Chamada n le)})
    <|> try (do {n <- float; return (Const (CDouble n))})
    <|> do {n <- natural; return (Const (CInt n))}
    <|> do {n <- stringLiteral; return (Const (CString n))}
    <|> do {n <- identifier; return (IdVar n)}
    <?> "simple expression"

partida :: Parsec String u Programa
partida = do {e <- programa; eof; return e}

parserE e = runParser partida [] "Expressoes" e

-- funcao para imprimir Prog com quebra de linha
printPrograma (Prog listaFuncao listaFuncaoBloco listaVars blocoPrincipal) = do {
    print "Prog:";
    print listaFuncao;
    print listaFuncaoBloco;
    print listaVars;
    print blocoPrincipal;
}

parserExpr s = case parserE s of
    Left er -> print er
    Right v -> print v -- printPrograma v

main = do {
    putStr "Expressão:";
    handle <- openFile "test.galu" ReadMode;
    e <- hGetContents handle;
    parserExpr e}

-- Ver com o prof
-- [Var] é para variaveis globais? Quando ler (entre, só antes?)
-- declaração dentro de bloco, quebra. Bloco principal aceita declaração e bloco normal não
-- precisavamos reconhecer True e False?