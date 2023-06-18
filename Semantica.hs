module Semantica where

-- Todo arrumar warning de conversao doubleInt
-- return de funcao n esta sendo valida com o tipo de retorno

import DataTypes
import Control.Monad (unless, when)

red = "\x1b[31m"
yellow = "\x1b[33m"
reset = "\x1b[0m"

newtype Semantica a = MS (String, a) deriving Show

instance Functor Semantica where
         fmap f (MS (s, a)) = MS (s, f a)

instance Applicative Semantica where
    pure x = MS ("", x)
    MS(s1, f) <*> MS(s2, x) = MS (s1 <> s2, f x)

instance Monad Semantica where
    MS(s, a) >>= f = let MS(s', b) = f a in MS (s++s', b)

erro s = MS (red    ++ "Error: "    ++ reset ++ s ++ "\n", ())
adv s = MS (yellow ++ "Warning: "  ++ reset ++ s ++ "\n", ())

semantica programa@(Prog lFuncao lFuncaoBloco lVars bPrincipal) = do
  bPrincipal1 <- normalizaDouble lFuncao lFuncaoBloco lVars bPrincipal
  lFuncaoBloco1 <- normalizaTipoRetorno lFuncao lFuncaoBloco lFuncao lFuncaoBloco
  bPrincipal3 <- normalizaDoubleR lFuncao lFuncaoBloco1 lVars bPrincipal1
  msgDeErroSo <- verificaTipoIncExprFuncao lFuncao lFuncaoBloco1 lFuncao lFuncaoBloco1
  msgDeAdvSo <- chamaVerificaDoubleIntFuncao lFuncao lFuncaoBloco1 lFuncao lFuncaoBloco1;
  msgDeErroSo <- verificaTipoIncExpr lFuncao lFuncaoBloco1 lVars bPrincipal3
  msgDeAdvSo <- verificaDoubleInt lFuncao lFuncaoBloco1 lVars bPrincipal3 "";
  msgDeErroSo <- verificaExiste lFuncao lFuncaoBloco1 lVars bPrincipal3 "";
  msgDeErroSo <- chamaVerificaExisteFuncao lFuncao lFuncaoBloco1 lFuncao lFuncaoBloco1;
  msgDeErroSo <- verificaSeVarRepete lVars "";
  msgDeErroSo <- verificaSeVarRepeteEmFuncao lFuncaoBloco1;
  msgDeErroSo <- verificaSeFuncaoRepete lFuncao;
  return (Prog lFuncao lFuncaoBloco1 lVars bPrincipal3)



verificaParametros [] _ _ _ = return []
verificaParametros (elem:xs) [] listaVars listaFuncoes = do {

     transformedRest <- verificaParametros xs [] listaVars listaFuncoes;
     return (elem : transformedRest)
 }
verificaParametros (elem:xs) ((_:#:tipo):tipos) listaVars listaFuncoes = do {
    transformedElem <- if tipo==TDouble then
        transformaDouble elem listaVars listaFuncoes
    else if tipo==TInt then
        transformaInt elem listaVars listaFuncoes elem
    else
        return elem;
    transformedRest <- verificaParametros xs tipos listaVars listaFuncoes;
    return (transformedElem : transformedRest)
}

transformaDouble (e1 :+: e2) listaVars listaFuncoes = do
                                                    transformedE1 <- transformaDouble e1 listaVars listaFuncoes;
                                                    transformedE2 <- transformaDouble e2 listaVars listaFuncoes;
                                                    return (transformedE1 :+: transformedE2)
transformaDouble (e1 :-: e2) listaVars listaFuncoes = do
                                                    transformedE1 <- transformaDouble e1 listaVars listaFuncoes;
                                                    transformedE2 <- transformaDouble e2 listaVars listaFuncoes;
                                                    return (transformedE1 :-: transformedE2)
transformaDouble (e1 :*: e2) listaVars listaFuncoes = do
                                                    transformedE1 <- transformaDouble e1 listaVars listaFuncoes;
                                                    transformedE2 <- transformaDouble e2 listaVars listaFuncoes;
                                                    return (transformedE1 :*: transformedE2)
transformaDouble (e1 :/: e2) listaVars listaFuncoes = do
                                                    transformedE1 <- transformaDouble e1 listaVars listaFuncoes;
                                                    transformedE2 <- transformaDouble e2 listaVars listaFuncoes;
                                                    return (transformedE1 :/: transformedE2)
transformaDouble (Neg e) listaVars listaFuncoes = do
                                                    transformedE1 <- transformaDouble e listaVars listaFuncoes;
                                                    return (Neg e)
transformaDouble e@(Const (CDouble _)) _ _ = return e
transformaDouble e@(Const (CInt _)) _ _ = do {
    return (IntDouble e)
}
transformaDouble e@(Chamada nome lExpr) listaVars listaFuncoes = do {
    transformedLExpr <- verificaParametros lExpr (getTipoParams nome listaFuncoes) listaVars listaFuncoes;
    if verificaSeDeclaracaoFuncaoDouble nome listaFuncoes then
        return (IntDouble (Chamada nome transformedLExpr))
    else
        return (Chamada nome transformedLExpr)
}
transformaDouble e@(IdVar nome) listaVars listaFuncoes = do {
    if verificaSeDeclaracaoDouble nome listaVars then
    return e;
    else
    return $ IntDouble e;
    }
transformaDouble e@(Lit str) listaVars listaFuncoes = do {
    return e;
}

transformaInt (e1 :+: e2) listaVars listaFuncoes elemCompleto = do
                                                transformedE1 <- transformaInt e1 listaVars listaFuncoes elemCompleto;
                                                transformedE2 <- transformaInt e2 listaVars listaFuncoes elemCompleto;
                                                return (transformedE1 :+: transformedE2);
transformaInt (e1 :-: e2) listaVars listaFuncoes elemCompleto = do
                                                transformedE1 <- transformaInt e1 listaVars listaFuncoes elemCompleto;
                                                transformedE2 <- transformaInt e2 listaVars listaFuncoes elemCompleto;
                                                return (transformedE1 :-: transformedE2);
transformaInt (e1 :*: e2) listaVars listaFuncoes elemCompleto = do
                                                transformedE1 <- transformaInt e1 listaVars listaFuncoes elemCompleto;
                                                transformedE2 <- transformaInt e2 listaVars listaFuncoes elemCompleto;
                                                return (transformedE1 :*: transformedE2);
transformaInt (e1 :/: e2) listaVars listaFuncoes elemCompleto = do
                                                transformedE1 <- transformaInt e1 listaVars listaFuncoes elemCompleto;
                                                transformedE2 <- transformaInt e2 listaVars listaFuncoes elemCompleto;
                                                return (transformedE1 :/: transformedE2);
transformaInt (Neg e) listaVars listaFuncoes elemCompleto = do
                                                transformedE <- transformaInt e listaVars listaFuncoes elemCompleto;
                                                return (Neg transformedE);
transformaInt e@(Const (CDouble _)) _ _ elemCompleto = do {
        return (DoubleInt e)
     }
transformaInt e@(Const (CInt _)) _ _ elemCompleto = return e
transformaInt e@(Chamada nome lExpr) listaVars listaFuncoes elemCompleto = do {
        transformedLExpr <- verificaParametros lExpr (getTipoParams nome listaFuncoes) listaVars listaFuncoes;
        if verificaSeDeclaracaoFuncaoDouble nome listaFuncoes then
            return (DoubleInt (Chamada nome transformedLExpr));
        else
            return (Chamada nome transformedLExpr);
    }
transformaInt e@(IdVar nome) listaVars listaFuncoes elemCompleto = do {
     if verificaSeDeclaracaoDouble nome listaVars then
        return (DoubleInt e);
     else
        return e;
     }
transformaInt e@(Lit str) listaVars listaFuncoes elemCompleto = do {
    return e;
}

normalizaDouble _ _ _ [] = return []
normalizaDouble declaracoesFuncao blocosFuncoes declaracaoMain (elem@(Atrib nome e):xs) = do
    if verificaSeDeclaracaoDouble nome declaracaoMain then do
        transformedE <- transformaDouble e declaracaoMain declaracoesFuncao
        normalizaDouble declaracoesFuncao blocosFuncoes declaracaoMain xs >>= \rest -> return (Atrib nome transformedE : rest)
    else do
        transformedE <- transformaInt e declaracaoMain declaracoesFuncao e
        normalizaDouble declaracoesFuncao blocosFuncoes declaracaoMain xs >>= \rest -> return (Atrib nome transformedE : rest)
normalizaDouble declaracoesFuncao blocosFuncoes declaracaoMain (elem:xs) = do
    normalizaDouble declaracoesFuncao blocosFuncoes declaracaoMain xs >>= \rest -> return (elem : rest)

chamaVerificaDoubleIntFuncao [] _ _ _ = return []
chamaVerificaDoubleIntFuncao _ [] _ _ = return []
chamaVerificaDoubleIntFuncao (declaracao@(nome :->: _):restoDeclaracao) ((_,_,bloco):restoBloco) declaracoesFuncao blocosFuncoes = do
    verifica <- verificaDoubleInt declaracoesFuncao blocosFuncoes declaracao bloco nome;
    rest <- chamaVerificaDoubleIntFuncao restoDeclaracao restoBloco declaracoesFuncao blocosFuncoes;
    return (verifica : rest);


verificaDoubleInt _ _ _ [] _ = return [];
verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain (elem@(Atrib nome e):xs) onde = do
    temDoubleInt <- verificaSeDoubleInt e declaracoesFuncao blocosFuncoes declaracaoMain;
    if temDoubleInt then do
        traduzidoE <- traduzExpr e;
        if onde == "" then do
            adv ("Conversão de double para inteiro dentro da Main em: "++nome++" = "++traduzidoE++";");
        else
            adv ("Conversão de double para inteiro dentro da função "++onde++" em: "++nome++" = "++traduzidoE++";");
        verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain xs onde >>= \rest -> return (elem : rest);
    else
        verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain xs onde >>= \rest -> return (elem : rest);
verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain (elem@(Ret (Just e)):xs) onde = do
    temDoubleInt <- verificaSeDoubleInt e declaracoesFuncao blocosFuncoes declaracaoMain;
    if temDoubleInt then do
        traduzidoE <- traduzExpr e;
        if onde == "" then do
            adv ("Conversão de double para inteiro dentro da Main em: return "++traduzidoE++";");
        else
            adv ("Conversão de double para inteiro dentro da função "++onde++" em: return "++traduzidoE++";");
        verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain xs onde >>= \rest -> return (elem : rest);
    else
        verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain xs onde >>= \rest -> return (elem : rest);
verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain (elem@(If _ bloco blocoElse):xs) onde = do {
     verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain bloco onde;
     verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain blocoElse onde;
     verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain xs onde >>= \rest -> return (elem : rest);
 }
verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain (elem@(While _ bloco):xs) onde = do {
     verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain bloco onde;
     verificaDoubleInt declaracoesFuncao blocosFuncoes declaracaoMain xs onde >>= \rest -> return (elem : rest);
 }

repeteFuncao _ [] = return False
repeteFuncao funcao (e@(nomeFuncao :->: _):xs) = if nomeFuncao==funcao then return True else repeteFuncao funcao xs

verificaSeFuncaoRepete [] = return []
verificaSeFuncaoRepete (x@(nomeFuncao :->: _):xs) = do {
    resu <- repeteFuncao nomeFuncao xs;
    when resu (erro ("Função "++nomeFuncao++" declarada mais de uma vez"));
    rest <- verificaSeFuncaoRepete xs;
    return (x : rest)
}

verificaSeVarRepeteEmFuncao [] = return []
verificaSeVarRepeteEmFuncao (x@(nome, dec, _):funcoes) = do {
    elem <- verificaSeVarRepete dec nome;
    rest <- verificaSeVarRepeteEmFuncao funcoes;
    return (elem:rest)
}

repeteVar _ [] = return False
repeteVar var (e@(nome :#: _):xs) = if nome==var then return True else repeteVar var xs

verificaSeVarRepete [] onde = return []
verificaSeVarRepete (x@(nome :#: _):xs) onde = do
    resu <- repeteVar nome xs
    if resu then do
        if onde=="" then
            erro ("Variável "++nome++" declarada mais de uma vez na Main")
        else
            erro ("Variável "++nome++" declarada mais de uma vez na função "++onde)
        rest <- verificaSeVarRepete xs onde
        return (x : rest)
    else do
        rest <- verificaSeVarRepete xs onde
        return (x : rest)

pegaPrimeiroElemFormatado ((IdVar nome):_) = return ("Variável "++nome);
pegaPrimeiroElemFormatado ((Chamada nome _):_) = return ("Função "++nome);

listaVazia [] = return True
listaVazia _ = return False

chamaVerificaExisteFuncao [] _ _ _ = return []
chamaVerificaExisteFuncao _ [] _ _ = return []
chamaVerificaExisteFuncao (declaracao@(nome :->: _):restoDeclaracao) ((_,dec,bloco):restoBloco) declaracoesFuncao blocosFuncoes = do
    verifica <- verificaExiste declaracoesFuncao blocosFuncoes dec bloco nome;
    rest <- chamaVerificaExisteFuncao restoDeclaracao restoBloco declaracoesFuncao blocosFuncoes;
    return (verifica : rest);

verificaExiste _ _ _ [] _ = return []
verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain (elem@(Atrib nome e):xs) onde = do
    varExiste <- verificaSeVarExiste nome declaracaoMain
    if varExiste then do
        listaExprComErro <- verificaSeExisteEmExpr e declaracoesFuncao blocosFuncoes declaracaoMain
        listaEVazia <- listaVazia listaExprComErro
        if not listaEVazia then do
            traduzidoE <- traduzExpr e
            elemNaoExiste <- pegaPrimeiroElemFormatado listaExprComErro
            if onde == "" then
                erro (elemNaoExiste++", não declarada dentro da Main em: "++nome++" = "++traduzidoE++";")
            else
                erro (elemNaoExiste++", não declarada dentro da função "++onde++" em: "++nome++" = "++traduzidoE++";")
            rest <- verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain xs onde
            return (elem : rest)
        else do
            rest <- verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain xs onde
            return (elem : rest)
    else do
        traduzidoE <- traduzExpr e
        if onde == "" then do
            erro ("Variável "++nome++", não declarada dentro da Main em: "++nome++" = "++traduzidoE++";")
        else
            erro ("Variável "++nome++", não declarada dentro da função "++onde++" em: "++nome++" = "++traduzidoE++";")
        rest <- verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain xs onde
        return (elem : rest)
verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain (elem@(Ret (Just e)):xs) onde = do
    listaExprComErro <- verificaSeExisteEmExpr e declaracoesFuncao blocosFuncoes declaracaoMain
    listaEVazia <- listaVazia listaExprComErro
    if not listaEVazia then do
        traduzidoE <- traduzExpr e
        elemNaoExiste <- pegaPrimeiroElemFormatado listaExprComErro
        if onde == "" then
            erro (elemNaoExiste++", não declarada dentro da Main em: return "++traduzidoE++";")
        else
            erro (elemNaoExiste++", não declarada dentro da função "++onde++" em: return "++traduzidoE++";")
        rest <- verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain xs onde
        return (elem : rest)
    else do
        rest <- verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain xs onde
        return (elem : rest)
verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain (elem@(If _ bloco blocoElse):xs) onde = do
    verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain bloco onde;
    verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain blocoElse onde;
    rest <- verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain xs onde
    return (elem : rest)
verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain (elem@(While _ bloco):xs) onde = do
    verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain bloco onde;
    rest <- verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain xs onde
    return (elem : rest)
verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain (elem:xs) onde = do
    rest <- verificaExiste declaracoesFuncao blocosFuncoes declaracaoMain xs onde
    return (elem : rest)

verificaSeVarExiste _ [] = return False
verificaSeVarExiste nome ((nomeVar :#: _):xs) = if nomeVar==nome then return True else verificaSeVarExiste nome xs

verificaSeFuncaoExiste _ [] = return False
verificaSeFuncaoExiste nome ((nomeFuncao :->: _):xs) = if nomeFuncao==nome then return True else verificaSeFuncaoExiste nome xs

verificaSeExisteEmListaExpr [] _ _ _ = return [];
verificaSeExisteEmListaExpr (x:xs) declaracoesFuncao blocosFuncoes declaracaoMain = do {
     transformed <- verificaSeExisteEmExpr x declaracoesFuncao blocosFuncoes declaracaoMain;
     rest <- verificaSeExisteEmListaExpr xs declaracoesFuncao blocosFuncoes declaracaoMain;
     return (transformed ++ rest);
 }

verificaSeExisteEmExpr (e1 :+: e2) declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaSeExisteEmExpr e1 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaSeExisteEmExpr e2 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 ++ transformedE2);
                                                     }
verificaSeExisteEmExpr (e1 :-: e2) declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaSeExisteEmExpr e1 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaSeExisteEmExpr e2 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 ++ transformedE2);
                                                     }
verificaSeExisteEmExpr (e1 :*: e2) declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaSeExisteEmExpr e1 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaSeExisteEmExpr e2 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 ++ transformedE2);
                                                     }
verificaSeExisteEmExpr (e1 :/: e2) declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                        transformedE1 <- verificaSeExisteEmExpr e1 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                        transformedE2 <- verificaSeExisteEmExpr e2 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                        return (transformedE1 ++ transformedE2);
                                                    }
verificaSeExisteEmExpr (Neg e) declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                        verificaSeExisteEmExpr e declaracoesFuncao blocosFuncoes declaracaoMain;
                                                    }
verificaSeExisteEmExpr e@(Const (CDouble _)) _ _ _ = return []
verificaSeExisteEmExpr e@(Const (CInt _)) _ _ _ = return []
verificaSeExisteEmExpr e@(Chamada nome params) declaracoesFuncao blocosFuncoes declaracaoMain = do {
    existeFuncao <- verificaSeFuncaoExiste nome declaracoesFuncao;
    if existeFuncao then do
        verificaSeExisteEmListaExpr params declaracoesFuncao blocosFuncoes declaracaoMain;
    else
        return [e]
}
verificaSeExisteEmExpr e@(IdVar nome) declaracoesFuncao blocosFuncoes declaracaoMain = do {
    varExiste <- verificaSeVarExiste nome declaracaoMain;
    if varExiste then
        return [];
    else
        return [e];
}
verificaSeExisteEmExpr e@(Lit _) _ _ _ = return []
verificaSeExisteEmExpr e@(DoubleInt elem) declaracoesFuncao blocosFuncoes declaracaoMain = do {
    verificaSeExisteEmExpr elem declaracoesFuncao blocosFuncoes declaracaoMain;
 }
verificaSeExisteEmExpr e@(IntDouble elem) declaracoesFuncao blocosFuncoes declaracaoMain = do {
    verificaSeExisteEmExpr elem declaracoesFuncao blocosFuncoes declaracaoMain;
 }

verificaSeDoubleInt (e1 :+: e2) declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaSeDoubleInt e1 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaSeDoubleInt e2 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 || transformedE2);
                                                     }
verificaSeDoubleInt (e1 :-: e2) declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaSeDoubleInt e1 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaSeDoubleInt e2 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 || transformedE2);
                                                     }
verificaSeDoubleInt (e1 :*: e2) declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaSeDoubleInt e1 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaSeDoubleInt e2 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 || transformedE2);
                                                     }
verificaSeDoubleInt (e1 :/: e2) declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaSeDoubleInt e1 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaSeDoubleInt e2 declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 || transformedE2);
                                                     }
verificaSeDoubleInt (Neg e) declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         verificaSeDoubleInt e declaracoesFuncao blocosFuncoes declaracaoMain;
                                                     }
verificaSeDoubleInt e@(Const (CDouble _)) _ _ _ = return False
verificaSeDoubleInt e@(Const (CInt _)) _ _ _ = return False
verificaSeDoubleInt e@(Chamada nome params) declaracoesFuncao blocosFuncoes declaracaoMain = do {
    doubleIntEmParams <- verificaSeDoubleIntEmParams params declaracoesFuncao blocosFuncoes declaracaoMain;
    paramsTraduzido <- traduzExprComoParams params;
    when doubleIntEmParams (erro ("Conversão de double para inteiro nos parametros da função: "++nome++"( "++paramsTraduzido++" )"));
    return False
 }
verificaSeDoubleInt e@(IdVar nome) declaracoesFuncao blocosFuncoes declaracaoMain = do {
     return False
 }
verificaSeDoubleInt e@(Lit _) _ _ _ = return False
verificaSeDoubleInt e@(DoubleInt elem) _ _ _ = do {
     return (True)
 }
verificaSeDoubleInt e _ _ _ = return False

verificaSeDoubleIntEmParams [] _ _ _ = return False
verificaSeDoubleIntEmParams (x:xs) declaracoesFuncao blocosFuncoes declaracaoMain = do {
     traduzido <- verificaSeDoubleInt x declaracoesFuncao blocosFuncoes declaracaoMain;
     rest <- verificaSeDoubleIntEmParams xs declaracoesFuncao blocosFuncoes declaracaoMain;
     return (traduzido || rest)
 }

verificaTipoIncExprFuncao [] [] _ _ = return []
verificaTipoIncExprFuncao (y:ys) ((_,declaracoes,bloco):xs) declaracoesFuncao blocosFuncoes = do {
    elem <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracoes bloco;
    rest <- verificaTipoIncExprFuncao ys xs declaracoesFuncao blocosFuncoes;
    return (elem : rest)
}

verificaTipoIncExpr _ _ _ [] = return []
verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain (elem@(Atrib nome e):xs) = do
    case getTipoVar nome declaracaoMain of
        Just tipo -> do {
             compartivel <- verificaTipoComExpr e tipo declaracoesFuncao blocosFuncoes declaracaoMain;
             if not compartivel then do
                 traduzidoE <- traduzExpr e
                 erro ("Tipos incompatíveis em: " ++ nome ++ " = " ++ traduzidoE ++ ";")
                 rest <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain xs
                 return (elem : rest)
             else do
                 rest <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain xs
                 return (elem : rest)
             }
        Nothing -> do
            traduzidoE <- traduzExpr e
            erro ("Variável " ++ nome ++ " não definida em: " ++ nome ++ " = " ++ traduzidoE ++ ";")
            rest <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain xs
            return (elem : rest)
verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain (elem@(If _ bloco blocoElse):xs) = do
    discart1 <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain bloco;
    discart2 <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain blocoElse;
    rest <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain xs;
    return (elem : rest);
verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain (elem@(While _ bloco):xs) = do
    discart1 <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain bloco;
    rest <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain xs;
    return (elem : rest);
verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain (elem@(Ret (Just exp)):xs) = do
            primeiroTipo <- getPriTipoComExpr exp declaracoesFuncao blocosFuncoes declaracaoMain;
            compartivel <- verificaTipoComExpr exp primeiroTipo declaracoesFuncao blocosFuncoes declaracaoMain;
            if not compartivel then do
                traduzidoE <- traduzExpr exp
                erro ("Tipos incompatíveis em: return " ++ traduzidoE ++ ";")
                rest <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain xs
                return (elem : rest)
            else do
                rest <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain xs
                return (elem : rest)
verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain (x:xs) = do {
     rest <- verificaTipoIncExpr declaracoesFuncao blocosFuncoes declaracaoMain xs;
     return (x : rest);
}

verificaTipoComExpr (e1 :+: e2) tipo declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaTipoComExpr e1 tipo declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaTipoComExpr e2 tipo declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 && transformedE2);
                                                     }
verificaTipoComExpr (e1 :-: e2) tipo declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaTipoComExpr e1 tipo declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaTipoComExpr e2 tipo declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 && transformedE2);
                                                     }
verificaTipoComExpr (e1 :*: e2) tipo declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaTipoComExpr e1 tipo declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaTipoComExpr e2 tipo declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 && transformedE2);
                                                     }
verificaTipoComExpr (e1 :/: e2) tipo declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         transformedE1 <- verificaTipoComExpr e1 tipo declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         transformedE2 <- verificaTipoComExpr e2 tipo declaracoesFuncao blocosFuncoes declaracaoMain;
                                                         return (transformedE1 && transformedE2);
                                                     }
verificaTipoComExpr (Neg e) tipo declaracoesFuncao blocosFuncoes declaracaoMain = do {
                                                         verificaTipoComExpr e tipo declaracoesFuncao blocosFuncoes declaracaoMain;
                                                     }
verificaTipoComExpr e@(Const (CDouble _)) tipo _ _ _ = return (tipo==TDouble || tipo==TInt)
verificaTipoComExpr e@(Const (CInt _)) tipo _ _ _ = return (tipo==TDouble || tipo==TInt)
verificaTipoComExpr e@(Chamada nome params) tipo declaracoesFuncao blocosFuncoes declaracaoMain = do {
    paramsCompativel <- verificaTipoParams params declaracoesFuncao blocosFuncoes declaracaoMain;
    paramsTraduzido <- traduzExprComoParams params;
    unless paramsCompativel (erro ("Tipos incompatíveis nos parametros da função: "++nome++"( "++paramsTraduzido++" )"));
    quantParams <- getQuantidadeParams nome declaracoesFuncao;
    when (quantParams > length params) (erro ("Quantidade a menos de parametros na chamada da função: "++nome++"( "++paramsTraduzido++" )"));
    when (quantParams < length params) (erro ("Quantidade a mais de parametros na chamada da função: "++nome++"( "++paramsTraduzido++" )"));
    tipoFuncao <- getTipoFuncao nome declaracoesFuncao;
    case tipoFuncao of
        Just tipoFuncao -> do {
         if tipoFuncao==TDouble || tipoFuncao==TInt then
             return (tipo==TDouble || tipo==TInt)
         else
             return (tipo==TString)
         }
        Nothing -> return False;

 }
verificaTipoComExpr e@(IdVar nome) tipo declaracoesFuncao blocosFuncoes declaracaoMain = do {
     tipoVar <- getTipoVar nome declaracaoMain;
     if tipoVar==TDouble || tipoVar==TInt then
         return (tipo==TDouble || tipo==TInt)
     else
         return (tipo==TString)
 }
verificaTipoComExpr e@(Lit _) tipo _ _ _ = return (tipo==TString)
verificaTipoComExpr e@(IntDouble elem) tipo _ _ _ = do {
     return (tipo==TDouble || tipo==TInt)
 }
verificaTipoComExpr e tipo _ _ _ = return (tipo==TDouble || tipo==TInt)

verificaTipoParams [] _ _ _ = return True
verificaTipoParams (x:xs) declaracoesFuncao blocosFuncoes declaracao = do {
     tipo <- getPriTipoComExpr x declaracoesFuncao blocosFuncoes declaracao;
     resu <- verificaTipoComExpr x tipo declaracoesFuncao blocosFuncoes declaracao;
     rest <- verificaTipoParams xs declaracoesFuncao blocosFuncoes declaracao;
     return (rest && resu)
 }

getPriTipoComExpr (e1 :+: e2) declaracoesFuncao blocosFuncoes declaracaoMain = getPriTipoComExpr e1 declaracoesFuncao blocosFuncoes declaracaoMain;
getPriTipoComExpr (e1 :-: e2) declaracoesFuncao blocosFuncoes declaracaoMain = getPriTipoComExpr e1 declaracoesFuncao blocosFuncoes declaracaoMain;
getPriTipoComExpr (e1 :*: e2) declaracoesFuncao blocosFuncoes declaracaoMain = getPriTipoComExpr e1 declaracoesFuncao blocosFuncoes declaracaoMain;
getPriTipoComExpr (e1 :/: e2) declaracoesFuncao blocosFuncoes declaracaoMain = getPriTipoComExpr e1 declaracoesFuncao blocosFuncoes declaracaoMain;
getPriTipoComExpr (Neg e) declaracoesFuncao blocosFuncoes declaracaoMain = getPriTipoComExpr e declaracoesFuncao blocosFuncoes declaracaoMain
getPriTipoComExpr e@(Const (CDouble _)) _ _ _ = return TDouble
getPriTipoComExpr e@(Const (CInt _)) _ _ _ = return TInt
getPriTipoComExpr e@(Chamada nome _) declaracoesFuncao blocosFuncoes declaracaoMain = do { -- ficar de olho
     tipo <- getTipoFuncao nome declaracoesFuncao;
     case tipo of
         Just tipo -> return tipo;
 }
getPriTipoComExpr e@(IdVar nome) declaracoesFuncao blocosFuncoes declaracaoMain = getTipoVar nome declaracaoMain
getPriTipoComExpr e@(Lit _) _ _ _ = return TString
getPriTipoComExpr e _ _ _ = return TInt

-- 1 parte retorno
normalizaTipoRetorno [] [] _ _ = return []
normalizaTipoRetorno ((nome :->: (_, tipo)):ys) ((_,declaracoes,bloco):xs) declaracoesFuncao blocosFuncoes = do {
     transformedBloco <- normalizaTipoRetorno' declaracoesFuncao blocosFuncoes declaracoes bloco tipo;
     rest <- normalizaTipoRetorno ys xs declaracoesFuncao blocosFuncoes;
     return ((nome, declaracoes, transformedBloco) : rest)
 }

normalizaTipoRetorno' _ _ _ [] _ = return []
normalizaTipoRetorno' declaracoesFuncao blocosFuncoes listaVars (elem@(Ret (Just e)):xs) tipo = do {
    if tipo==TDouble then do
        transformedE <- transformaDouble e listaVars declaracoesFuncao;
        normalizaTipoRetorno' declaracoesFuncao blocosFuncoes listaVars xs tipo >>= \rest -> return (Ret (Just transformedE) : rest)
    else if tipo==TInt then do
        transformedE <- transformaInt e listaVars declaracoesFuncao e;
        normalizaTipoRetorno' declaracoesFuncao blocosFuncoes listaVars xs tipo >>= \rest -> return (Ret (Just transformedE) : rest)
    else do
        traduzidoE <- traduzExpr e
        erro ("Tipo de retorno incompativel em: "++traduzidoE);
        normalizaTipoRetorno' declaracoesFuncao blocosFuncoes listaVars xs tipo >>= \rest -> return (elem : rest);
}
normalizaTipoRetorno' declaracoesFuncao blocosFuncoes listaVars (elem:xs) tipo = do
    normalizaTipoRetorno' declaracoesFuncao blocosFuncoes listaVars xs tipo >>= \rest -> return (elem : rest);


verificaExprDouble (e1 :+: e2) listaVars listaFuncoes = do {
                                                         transformedE1 <- verificaExprDouble e1 listaVars listaFuncoes;
                                                         transformedE2 <- verificaExprDouble e2 listaVars listaFuncoes;
                                                         return (transformedE1 || transformedE2);
                                                     }
verificaExprDouble (e1 :-: e2) listaVars listaFuncoes = do {
                                                         transformedE1 <- verificaExprDouble e1 listaVars listaFuncoes;
                                                         transformedE2 <- verificaExprDouble e2 listaVars listaFuncoes;
                                                         return (transformedE1 || transformedE2);
                                                     }
verificaExprDouble (e1 :*: e2) listaVars listaFuncoes = do {
                                                         transformedE1 <- verificaExprDouble e1 listaVars listaFuncoes;
                                                         transformedE2 <- verificaExprDouble e2 listaVars listaFuncoes;
                                                         return (transformedE1 || transformedE2);
                                                     }
verificaExprDouble (e1 :/: e2) listaVars listaFuncoes = do {
                                                         transformedE1 <- verificaExprDouble e1 listaVars listaFuncoes;
                                                         transformedE2 <- verificaExprDouble e2 listaVars listaFuncoes;
                                                         return (transformedE1 || transformedE2);
                                                     }
verificaExprDouble (Neg e) listaVars listaFuncoes = do {
                                                         verificaExprDouble e listaVars listaFuncoes;
                                                     }
verificaExprDouble e@(Const (CDouble _)) _ _ = return True
verificaExprDouble e@(Const (CInt _)) _ _ = return False
verificaExprDouble e@(Chamada nome _) listaVars listaFuncoes = return (verificaSeDeclaracaoFuncaoDouble nome listaFuncoes)
verificaExprDouble e@(IdVar nome) listaVars listaFuncoes = return (verificaSeDeclaracaoDouble nome listaVars)
verificaExprDouble e@(Lit _) _ _ = return False

transformaExprRDouble (e1@(Lit _) :==: e2@(Lit _)) listaVars listaFuncoes = return (e1 :==: e2)
transformaExprRDouble (e1@(Lit _) :==: e2) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " == " ++ traduzidoE2)
                                                        return (e1 :==: e2)
transformaExprRDouble (e1 :==: e2@(Lit _)) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " == " ++ traduzidoE2)
                                                        return (e1 :==: e2)
transformaExprRDouble (e1 :==: e2) listaVars listaFuncoes = do {
                                                        transformedE1 <- transformaDouble e1 listaVars listaFuncoes;
                                                        transformedE2 <- transformaDouble e2 listaVars listaFuncoes;
                                                        return (transformedE1 :==: transformedE2);
                                                    }
transformaExprRDouble (e1@(Lit _) :/=: e2@(Lit _)) listaVars listaFuncoes = return (e1 :/=: e2)
transformaExprRDouble (e1@(Lit _) :/=: e2) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " /= " ++ traduzidoE2)
                                                        return (e1 :/=: e2)
transformaExprRDouble (e1 :/=: e2@(Lit _)) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " /= " ++ traduzidoE2)
                                                        return (e1 :/=: e2)
transformaExprRDouble (e1 :/=: e2) listaVars listaFuncoes = do {
                                                        transformedE1 <- transformaDouble e1 listaVars listaFuncoes;
                                                        transformedE2 <- transformaDouble e2 listaVars listaFuncoes;
                                                        return (transformedE1 :/=: transformedE2);
                                                    }
transformaExprRDouble (e1@(Lit _) :<=: e2@(Lit _)) listaVars listaFuncoes = return (e1 :<=: e2)
transformaExprRDouble (e1@(Lit _) :<=: e2) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " <= " ++ traduzidoE2)
                                                        return (e1 :<=: e2)
transformaExprRDouble (e1 :<=: e2@(Lit _)) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " <= " ++ traduzidoE2)
                                                        return (e1 :<=: e2)
transformaExprRDouble (e1 :<=: e2) listaVars listaFuncoes = do {
                                                        transformedE1 <- transformaDouble e1 listaVars listaFuncoes;
                                                        transformedE2 <- transformaDouble e2 listaVars listaFuncoes;
                                                        return (transformedE1 :<=: transformedE2);
                                                    }
transformaExprRDouble (e1@(Lit _) :>=: e2@(Lit _)) listaVars listaFuncoes = return (e1 :>=: e2)
transformaExprRDouble (e1@(Lit _) :>=: e2) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " >= " ++ traduzidoE2)
                                                        return (e1 :>=: e2)
transformaExprRDouble (e1 :>=: e2@(Lit _)) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " >= " ++ traduzidoE2)
                                                        return (e1 :>=: e2)
transformaExprRDouble (e1 :>=: e2) listaVars listaFuncoes =  do {
                                                        transformedE1 <- transformaDouble e1 listaVars listaFuncoes;
                                                        transformedE2 <- transformaDouble e2 listaVars listaFuncoes;
                                                        return (transformedE1 :>=: transformedE2);
                                                    }
transformaExprRDouble (e1@(Lit _) :<: e2@(Lit _)) listaVars listaFuncoes = return (e1 :<: e2)
transformaExprRDouble (e1@(Lit _) :<: e2) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " < " ++ traduzidoE2)
                                                        return (e1 :<: e2)
transformaExprRDouble (e1 :<: e2@(Lit _)) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " < " ++ traduzidoE2)
                                                        return (e1 :<: e2)
transformaExprRDouble (e1 :<: e2) listaVars listaFuncoes =  do {
                                                        transformedE1 <- transformaDouble e1 listaVars listaFuncoes;
                                                        transformedE2 <- transformaDouble e2 listaVars listaFuncoes;
                                                        return (transformedE1 :<: transformedE2);
                                                    }
transformaExprRDouble (e1@(Lit _) :>: e2@(Lit _)) listaVars listaFuncoes = return (e1 :>: e2)
transformaExprRDouble (e1@(Lit _) :>: e2) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " > " ++ traduzidoE2)
                                                        return (e1 :>: e2)
transformaExprRDouble (e1 :>: e2@(Lit _)) listaVars listaFuncoes = do
                                                        traduzidoE1 <- traduzExpr e1
                                                        traduzidoE2 <- traduzExpr e2
                                                        erro ("Expressão relacional incompativel em: " ++ traduzidoE1 ++ " > " ++ traduzidoE2)
                                                        return (e1 :>: e2)
transformaExprRDouble (e1 :>: e2) listaVars listaFuncoes =  do {
                                                        transformedE1 <- transformaDouble e1 listaVars listaFuncoes;
                                                        transformedE2 <- transformaDouble e2 listaVars listaFuncoes;
                                                        return (transformedE1 :>: transformedE2);
                                                    }


verificaExprRDouble e@(e1 :==: e2) listaVars listaFuncoes = do {
    res1 <- verificaExprDouble e1 listaVars listaFuncoes;
    res2 <- verificaExprDouble e2 listaVars listaFuncoes;
    if res1 || res2 then
        transformaExprRDouble e listaVars listaFuncoes
    else
        return e
 }
verificaExprRDouble e@(e1 :/=: e2) listaVars listaFuncoes = do {
    res1 <- verificaExprDouble e1 listaVars listaFuncoes;
    res2 <- verificaExprDouble e2 listaVars listaFuncoes;
    if res1 || res2 then
        transformaExprRDouble e listaVars listaFuncoes
    else
        return e
 }
verificaExprRDouble e@(e1 :<=: e2) listaVars listaFuncoes = do {
    res1 <- verificaExprDouble e1 listaVars listaFuncoes;
    res2 <- verificaExprDouble e2 listaVars listaFuncoes;
    if res1 || res2 then
        transformaExprRDouble e listaVars listaFuncoes
    else
        return e
 }
verificaExprRDouble e@(e1 :>=: e2) listaVars listaFuncoes = do {
    res1 <- verificaExprDouble e1 listaVars listaFuncoes;
    res2 <- verificaExprDouble e2 listaVars listaFuncoes;
    if res1 || res2 then
        transformaExprRDouble e listaVars listaFuncoes
    else
        return e
 }
verificaExprRDouble e@(e1 :<: e2) listaVars listaFuncoes = do {
    res1 <- verificaExprDouble e1 listaVars listaFuncoes;
    res2 <- verificaExprDouble e2 listaVars listaFuncoes;
    if res1 || res2 then
        transformaExprRDouble e listaVars listaFuncoes
    else
        return e
 }
verificaExprRDouble e@(e1 :>: e2) listaVars listaFuncoes = do {
    res1 <- verificaExprDouble e1 listaVars listaFuncoes;
    res2 <- verificaExprDouble e2 listaVars listaFuncoes;
    if res1 || res2 then
        transformaExprRDouble e listaVars listaFuncoes
    else
        return e
 }

verificaExprLDouble (e1 :&: e2) listaVars listaFuncoes = do {
                                                            transformedE1 <- verificaExprLDouble e1 listaVars listaFuncoes;
                                                            transformedE2 <- verificaExprLDouble e2 listaVars listaFuncoes;
                                                            return (transformedE1 :&: transformedE2)
                                                         }
verificaExprLDouble (e1 :|: e2) listaVars listaFuncoes = do {
                                                            transformedE1 <- verificaExprLDouble e1 listaVars listaFuncoes;
                                                            transformedE2 <- verificaExprLDouble e2 listaVars listaFuncoes;
                                                            return (transformedE1 :|: transformedE2)
                                                         }
verificaExprLDouble (Not e) listaVars listaFuncoes =  do {
                                                            transformedE <- verificaExprLDouble e listaVars listaFuncoes;
                                                            return (Not transformedE)
                                                         }
verificaExprLDouble (Rel expR) listaVars listaFuncoes = do {
    transformedExpR <- verificaExprRDouble expR listaVars listaFuncoes;
    return (Rel transformedExpR)
 }

normalizaDoubleR _ _ _ [] = return []
normalizaDoubleR declaracoesFuncao blocosFuncoes declaracaoMain (elem@(If exprL bloco blocoElse):xs) = do {
        transformedExprL <- verificaExprLDouble exprL declaracaoMain declaracoesFuncao;
        transformedBloco <- normalizaDouble declaracoesFuncao blocosFuncoes declaracaoMain bloco;
        transformedBlocoElse <- normalizaDouble declaracoesFuncao blocosFuncoes declaracaoMain blocoElse;
        rest <- normalizaDoubleR declaracoesFuncao blocosFuncoes declaracaoMain xs;
        return (If transformedExprL transformedBloco transformedBlocoElse : rest)
    }
normalizaDoubleR declaracoesFuncao blocosFuncoes declaracaoMain (elem@(While exprL bloco):xs) = do {
        transformedExprL <- verificaExprLDouble exprL declaracaoMain declaracoesFuncao;
        transformedBloco <- normalizaDouble declaracoesFuncao blocosFuncoes declaracaoMain bloco;
        rest <- normalizaDoubleR declaracoesFuncao blocosFuncoes declaracaoMain xs;
        return (While transformedExprL transformedBloco : rest)
    }
normalizaDoubleR declaracoesFuncao blocosFuncoes declaracaoMain (elem:xs) = do {
         rest <- normalizaDoubleR declaracoesFuncao blocosFuncoes declaracaoMain xs;
         return (elem : rest)
     }


verificaSeDeclaracaoDouble _ [] = False
verificaSeDeclaracaoDouble var ((nome :#: TDouble):xs) = (var == nome) || verificaSeDeclaracaoDouble var xs
verificaSeDeclaracaoDouble var (x:xs) = verificaSeDeclaracaoDouble var xs

verificaSeDeclaracaoFuncaoDouble _ [] = False
verificaSeDeclaracaoFuncaoDouble var (nome :->: (_,TDouble):xs) = (var == nome) || verificaSeDeclaracaoFuncaoDouble var xs
verificaSeDeclaracaoFuncaoDouble var (x:xs) = verificaSeDeclaracaoFuncaoDouble var xs

verificaSeDeclaracaoFuncaoInt _ [] = False
verificaSeDeclaracaoFuncaoInt var (nome :->: (_,TInt):xs) = (var == nome) || verificaSeDeclaracaoFuncaoInt var xs
verificaSeDeclaracaoFuncaoInt var (x:xs) = verificaSeDeclaracaoFuncaoInt var xs

traduzExpr (e1 :+: e2) = do {
                            transformedE1 <- traduzExpr e1;
                            transformedE2 <- traduzExpr e2;
                            return (transformedE1++" + "++transformedE2);
                        }
traduzExpr (e1 :-: e2) = do {
                            transformedE1 <- traduzExpr e1;
                            transformedE2 <- traduzExpr e2;
                            return (transformedE1++" - "++transformedE2);
                        }
traduzExpr (e1 :*: e2) = do {
                            transformedE1 <- traduzExpr e1;
                            transformedE2 <- traduzExpr e2;
                            return (transformedE1++" * "++transformedE2);
                        }
traduzExpr (e1 :/: e2) = do {
                            transformedE1 <- traduzExpr e1;
                            transformedE2 <- traduzExpr e2;
                            return (transformedE1++" / "++transformedE2);
                        }
traduzExpr (Neg e) = do {
                        return ("- "++show e);
                    }
traduzExpr e@(Const (CDouble v)) = return (show v)
traduzExpr e@(Const (CInt v)) = return (show v)
traduzExpr e@(Chamada nome v) = do {
     translatedV <- mapM traduzExpr v;
     return (nome++"("++unwords translatedV++")")
 }
traduzExpr e@(IdVar nome) = return nome;
traduzExpr e@(Lit v) = return ("'"++v++"'");
traduzExpr e@(IntDouble e1) = do { traduzExpr e1; }
traduzExpr e@(DoubleInt e1) = do { traduzExpr e1; }

traduzExprComoParams [] = return ""
traduzExprComoParams (x:[]) = do {
     traduzExpr x;
 }
traduzExprComoParams (x:xs) = do {
     traduzidoE <- traduzExpr x;
     rest <- traduzExprComoParams xs;
     return (traduzidoE ++ ", " ++ rest)
 }

getTipoVar _ [] = return TVoid
getTipoVar nome ((nomeVar :#: tipo):restoDec) = if nomeVar==nome then return tipo else getTipoVar nome restoDec;

getTipoParams nome ((nomeFuncao :->: (listaVars,_)):funcoes) = if nome==nomeFuncao then listaVars else getTipoParams nome funcoes

getTipoFuncao nome [] = return Nothing
getTipoFuncao nome ((nomeFuncao :->: (_,tipo)):funcoes) = if nome==nomeFuncao then return (Just tipo) else getTipoFuncao nome funcoes

getQuantidadeParams _ [] = return 0
getQuantidadeParams nome ((nomeFuncao :->: (listaVars,_)):funcoes) = if nome==nomeFuncao then return (length listaVars) else getQuantidadeParams nome funcoes