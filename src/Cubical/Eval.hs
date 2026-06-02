module Cubical.Eval
    ( eval
    , equivDom
    , isTopDNF, isBotDNF
    ) where

import Cubical.Interval (dnfTop, dnfBot, evalInterval, I(..))
import Cubical.Syntax

--------------------------------------------------------------------------------
-- DNF Helpers
--------------------------------------------------------------------------------

isTopDNF :: Term -> Bool
isTopDNF (TCube d) = d == dnfTop
isTopDNF _         = False

isBotDNF :: Term -> Bool
isBotDNF (TCube d) = d == dnfBot
isBotDNF _         = False

--------------------------------------------------------------------------------
-- Evaluator
--------------------------------------------------------------------------------

-- Forward declaration: definitionallyEqual lives in Equality, but eval needs
-- it for the transport trivial-path check. We break the cycle by inlining a
-- syntactic structural equality here (eval-time only; no eta).
syntacticEq :: Term -> Term -> Bool
syntacticEq = (==)

eval :: Term -> Term
eval t = case t of
    TApp f a ->
        case eval f of
            TAbs _ body -> eval (beta body (eval a))
            f'          -> TApp f' (eval a)

    PApp p r ->
        let r' = eval r
        in case eval p of
            PLam _ body -> eval (beta body r')
            p'          -> PApp p' r'

    TAbs x b    -> TAbs x (eval b)
    TPi x a b   -> TPi x (eval a) (eval b)
    TPath a u v -> TPath (eval a) (eval u) (eval v)
    PLam i b    -> PLam i (eval b)
    TInterval i -> TCube (evalInterval i)

    THComp aTy phi tube base ->
        let phi' = eval phi
        in if isTopDNF phi'
           then case eval tube of
                    PLam _ body -> eval (beta body (TInterval I1))
                    tube'       -> PApp tube' (TInterval I1)
           else if isBotDNF phi'
           then eval base
           else THComp (eval aTy) phi' (eval tube) (eval base)

    TEquiv a b ->
        TEquiv (eval a) (eval b)

    TMkEquiv a b f g eta eps ->
        TMkEquiv (eval a) (eval b) (eval f) (eval g) (eval eta) (eval eps)

    TEquivFwd e x ->
        let e' = eval e; x' = eval x
        in case e' of
            TMkEquiv _ _ f _ _ _ -> eval (TApp f x')
            _                    -> TEquivFwd e' x'

    TUa e -> TUa (eval e)

    TTransport p x ->
        let p' = eval p; x' = eval x
        in case p' of

            -- ua e : Path U A B  →  transport (ua e) x  =  equivFwd e x
            TUa e -> eval (TEquivFwd e x')

            PLam iName body ->
                let b0 = eval (beta body (TInterval I0))
                    b1 = eval (beta body (TInterval I1))
                in if syntacticEq b0 b1
                   -- Trivial (constant) path: transport is identity
                   then x'

                   else case (b0, b1) of

                       -- Pi transport:
                       --   p i = Π(a : A i). B i a
                       --
                       -- Full CCHM rule:
                       --   transport p f = λ a₁.
                       --     let a₀    = transport (⟨i⟩ A (1−i)) a₁
                       --         fillᵢ = transport (⟨j⟩ A (i∧j)) a₀
                       --     in  transport (⟨i⟩ B i fillᵢ) (f a₀)
                       --
                       -- The reverse transport  transport (⟨i⟩ A (1−i))  and the
                       -- fill  transport (⟨j⟩ A (i∧j))  cannot be expressed in
                       -- this term model without symbolic interval negation/meet
                       -- in the PLam binder (PLam binds at term level, not IVar
                       -- level, so ⟨i⟩ A(1−i) has no representation as a PLam).
                       --
                       -- Non-dependent codomain (B does not mention a):
                       --   transport (⟨i⟩ Π(a:A).B i) f = λ a. transport (⟨i⟩ B i) (f a)
                       -- This is the only case we can implement correctly here.
                       -- All other cases are left stuck (returned as-is), which is
                       -- the honest behaviour — a wrong reduction would be unsound.
                       (TPi argName _ _, TPi _ _ _) ->
                           -- B-family: ⟨i⟩ B i
                           -- Inside PLam iName, body's binder i = TVar 0.
                           -- beta (shift 1 0 body) (TVar 0) is the identity on body
                           -- (shift raises i to TVar 1; beta at 0 is a no-op; shift
                           -- -1 brings it back), so the PLam body is exactly body
                           -- with its TVar 0 still live — correct for a PLam in i.
                           let bFam = PLam iName $
                                   case eval (beta (shift 1 0 body) (TVar 0)) of
                                       TPi _ _ bI -> bI   -- B i, with i = TVar 0
                                       _          -> shift 1 0 b0B
                               -- Check whether B is non-dependent in a (TVar 0).
                               -- b0 = Π(a:A 0). B 0 a; the body B 0 a is b0Body,
                               -- which is open in a = TVar 0.  B is non-dependent iff
                               -- TVar 0 does not appear free in b0Body.
                               -- We test this by substituting TVar 0 with a sentinel
                               -- TUniv 0 and checking the result is unchanged; if TVar 0
                               -- is free, the substitution changes the term.
                               bNonDep = case b0 of
                                   TPi _ _ b0Body ->
                                       subst 0 (TUniv 0) b0Body == b0Body
                                   _ -> False
                           in if bNonDep
                              -- Non-dependent B: safe full reduction.
                              --   transport (⟨i⟩ Π(a:A).B i) f = λ a. transport (⟨i⟩ B i) (f a)
                              then TAbs argName $
                                       eval (TTransport bFam
                                               (eval (TApp (shift 1 0 x') (TVar 0))))
                              -- Dependent B: stuck — we cannot compute the backward
                              -- transport or fill without symbolic interval ops.
                              else TTransport p' x'
                           where
                               b0B = case b0 of TPi _ _ b -> b; _ -> b0

                       -- Path transport:
                       --   p i = Path (A i) (u i) (v i)
                       --   transport p q = ⟨j⟩ transport (⟨i⟩ A i) (q @ j)
                       --
                       -- Each point q@j : A 0 is transported to A 1.
                       -- The endpoints land at (transport (⟨i⟩ A i) (u 0))
                       -- and (transport (⟨i⟩ A i) (v 0)), which definitionally
                       -- equal u 1 and v 1 when A,u,v are well-typed.
                       (TPath tyA0 _ _, TPath _ _ _) ->
                           -- Extract the type family A : 𝕀 → U from the body.
                           -- body at i has shape  TPath (A i) (u i) (v i)
                           -- so we reconstruct ⟨i⟩ A i by projecting the type
                           -- component (first arg of TPath).
                           let aFam = PLam iName $
                                   case eval (beta (shift 1 0 body) (TVar 0)) of
                                       TPath a _ _ -> a
                                       _           -> shift 1 0 tyA0
                               -- j is a fresh interval variable (de Bruijn 0
                               -- after we enter the PLam below; aFam is shifted
                               -- to account for the new binder).
                               aFamS = shift 1 0 aFam
                           in PLam "j" $
                               eval (TTransport aFamS
                                       (PApp (shift 1 0 x') (TVar 0)))

                       -- Sigma transport:
                       --   p i = Σ(x : A i). B i x
                       --   transport p (a , b) =
                       --     let a' = transport (⟨i⟩ A i)           a
                       --         b' = transport (⟨i⟩ B i (fill A a i)) b
                       --     in  (a' , b')
                       --
                       --   fill (⟨i⟩ A i) a i  =  transport (⟨j⟩ A (i ∧ j)) a
                       --   This is the canonical fill defined via hcomp/transport.
                       (TSigma _ _ _, TSigma _ _ _) ->
                           case x' of
                             TPair a b ->
                               -- A-family: ⟨i⟩ A i  (project first component of body)
                               let aFam = PLam iName $
                                       case eval (beta (shift 1 0 body) (TVar 0)) of
                                           TSigma _ aI _ -> aI
                                           _             -> shift 1 0 b0A
                                   -- transport along A
                                   a' = eval (TTransport aFam a)
                                   -- B-family along fill: ⟨i⟩ B i (fill A a i)
                                   bFam = PLam iName $
                                       case eval (beta (shift 1 0 body) (TVar 0)) of
                                           TSigma _ _ bI ->
                                               -- bI : B i, binder i = TVar 0
                                               -- apply to (fill A a i):
                                               -- fill at i=TVar 0: transport (⟨j⟩ A (0∧j)) a
                                               let fillAtI = eval (TTransport
                                                       (PLam "j" $
                                                           eval (PApp (shift 2 0 aFam)
                                                               (TInterval (Meet (IVar 1) (IVar 0)))))
                                                       (shift 1 0 a))
                                               in eval (beta bI fillAtI)
                                           _ -> shift 1 0 b0B
                                   b' = eval (TTransport bFam b)
                               in TPair a' b'
                             -- non-pair: stuck
                             _ -> TTransport p' x'
                           where
                             b0A = case b0 of TSigma _ a _ -> a; _ -> b0
                             b0B = case b0 of TSigma _ _ bz -> bz; _ -> b0

                       -- Glue degenerate cases:
                       --   phi = 0  →  Glue A [0] te  =  A,  transport as usual
                       --   phi = 1  →  Glue A [1] te  =  dom(te),  transport via equiv
                       (TGlue aTy0 phi0 te0, TGlue _ _ _) ->
                           if isBotDNF (eval phi0)
                           then eval (TTransport
                                       (PLam iName $
                                           case eval (beta (shift 1 0 body) (TVar 0)) of
                                               TGlue a _ _ -> a
                                               other       -> other)
                                       x')
                           else if isTopDNF (eval phi0)
                           then eval (TTransport
                                       (PLam iName $
                                           case eval (beta (shift 1 0 body) (TVar 0)) of
                                               TGlue _ _ te -> equivDom (eval te)
                                               other        -> other)
                                       x')
                           else TTransport p' x'   -- general Glue: stuck

                       -- Everything else: stuck
                       _ -> TTransport p' x'

            -- Non-lambda path: stuck
            _ -> TTransport p' x'

    TGlue aTy phi te ->
        let phi' = eval phi
        in if isTopDNF phi'
           then equivDom (eval te)
           else if isBotDNF phi'
           then eval aTy
           else TGlue (eval aTy) phi' (eval te)

    TGlueElem phi t a ->
        let phi' = eval phi
        in if isTopDNF phi'
           then eval t
           else if isBotDNF phi'
           then eval a
           else TGlueElem phi' (eval t) (eval a)

    TUnglue phi te g ->
        let phi' = eval phi
        in if isTopDNF phi'
           then eval (TEquivFwd (eval te) (eval g))
           else if isBotDNF phi'
           then eval g
           else TUnglue phi' (eval te) (eval g)

    TSigma x a b -> TSigma x (eval a) (eval b)

    TPair a b -> TPair (eval a) (eval b)

    -- fst (a , b)  →  a
    TFst p ->
        case eval p of
            TPair a _ -> a
            p'        -> TFst p'

    -- snd (a , b)  →  b
    TSnd p ->
        case eval p of
            TPair _ b -> b
            p'        -> TSnd p'

    _ -> t

-- | Extract the domain type from an equivalence term.
equivDom :: Term -> Term
equivDom (TMkEquiv a _ _ _ _ _) = a
equivDom (TEquiv a _)           = a
equivDom other                  = other