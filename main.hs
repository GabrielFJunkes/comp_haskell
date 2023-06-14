-- Gabriel Felipe Junkes e Luciano de Abreu
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import System.IO

import DataTypes
import Semantica


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

montaVarsTipo _ [] = []
montaVarsTipo t (n:ln) = (n :#: t) : montaVarsTipo t ln

varBlocoPrincipal = do {
    t <- defineTipo;
    n <- commaSep1 identifier;
    semi;
    return (montaVarsTipo t n)
}

blocoPrincipal' = do {
    lv <- many varBlocoPrincipal;
    lc <- listaCmd;
    return (concat lv, lc)
}

blocoPrincipal = do {
    braces blocoPrincipal';
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
            lfv <- blocoPrincipal;
            lfb <- funcaoEBloco;
            return ((f,lfv) : lfb);
        }
        <|> return [];


funcaoId (id :->: _) = id
funcaoVar (_ :->: (vars, _)) = vars

retornaFuncao [] = []
retornaFuncao ((f, _):t) = f : retornaFuncao t

somaVars [] ys = ys
somaVars (x:xs) ys = x:somaVars ys xs

retornaIdVarBloco :: [(Funcao, ([Var], Bloco))] -> [(Id, [Var], Bloco)]
retornaIdVarBloco [] = []
retornaIdVarBloco ((f,(lv, b)):t) = (funcaoId f, somaVars (funcaoVar f) lv, b) : retornaIdVarBloco t

retornaListaVarDeBlocoPrincipal (lv, _) = lv
retornaBlocoDeBlocoPrincipal (_, b) = b

-- data Programa = Prog [Funcao] [(Id, [Var], Bloco)] [Var] Bloco deriving Show
programa = do
            lfb <- funcaoEBloco;
            let lf = retornaFuncao lfb;
            let idVarBloco = retornaIdVarBloco lfb;
            b <- blocoPrincipal;
            return (Prog lf idVarBloco (retornaListaVarDeBlocoPrincipal b) (retornaBlocoDeBlocoPrincipal b));

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
commaSep1 = T.commaSep1 lexico

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
    <|> do {n <- stringLiteral; return (Lit n)}
    <|> do {n <- identifier; return (IdVar n)}
    <?> "simple expression"

partida :: Parsec String u Programa
partida = do {e <- programa; eof; return e}

parserE e = runParser partida [] "Expressoes" e

-- funcao para imprimir Prog com quebra de linha (para debug)
printPrograma (Prog listaFuncao listaFuncaoBloco listaVars blocoPrincipal) = do {
    print "Prog:";
    print listaFuncao;
    print listaFuncaoBloco;
    print listaVars;
    print blocoPrincipal;
}

printSemantica' p = do putStrLn (fst p)
                       printPrograma (snd p)

printSemantica p = do let sem = semantica p
                      case sem of
                        MS p -> printSemantica' p

parserExpr s = case parserE s of
    Left er -> print er
    Right v -> printSemantica v

main = do {
    handle <- openFile "test.galu" ReadMode;
    e <- hGetContents handle;
    parserExpr e}



