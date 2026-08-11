{-# LANGUAGE ScopedTypeVariables #-}

-- | A literal, explicit-datatype companion to @agda\/src\/OpSem.agda@ (Fig.
-- 5-7 of the arXiv paper \/ Appendix A.3): the small-step (@_⊢_-[_]→_@) and
-- big-step (@_⊢_⇒[_]_@) operational semantics of the core \(\lambda_C\)
-- fragment, realised here as an actual, runnable reduction engine
-- ('step' \/ 'run') rather than a shallow Haskell-native embedding (that is
-- what @SelectionMonadHat.hs@ already does for the *denotational* Ŝ\/Ŵ
-- construction; this file instead needs the source language's own AST,
-- because rule R5 reifies a slice of the *evaluation context itself* into
-- an object-language value, which a shallow embedding cannot express).
--
-- What is dropped, and why it's safe to drop:
--
--   * Every dependent type index of Syntax.agda\/OpSem.agda (@Cxt@, @Ty@,
--     @EffCxt@, and the well-typedness they enforce) is erased. Those
--     indices exist in Agda purely so the AST can only represent
--     well-typed terms; they carry no information the *reduction* rules
--     themselves consult (no rule below ever pattern-matches on a type or
--     an effect-context membership witness for anything other than "which
--     concrete label does this operation\/handler carry", which is
--     realised here directly via @eff@\/@Eq eff@). Concretely this means:
--     variables are bare de Bruijn 'Int's (Subst.agda's @Ren@\/@Sub@ ported
--     as @Int -> Int@ \/ @Int -> Val@), and @Frame@\/@SFrame@\/@ContCxt@
--     drop their four type indices, becoming the 'KFrame'\/'Kont' below.
--
--   * @PrimFun@ (Domains.agda's @Sig@ field) is realised directly as a
--     Haskell function @Ground base r -> Ground base r@ rather than a
--     separate name\/semantics pair -- the object language embeds actual
--     host-language closures for primitives, exactly as 'SelectionMonadHat'
--     does for effect operations.
--
--   * R2-fst\/R2-snd project a value-level @vpair@ (not the expression
--     former @pair e1 e2@ mid-decomposition), and a new coalescing rule
--     (R2-pair) turns @pair (val v) (val w)@ into @val (vpair v w)@ once
--     both components are values -- this is what lets a value-level
--     product built via @pair e1 e2@ flow through a variable (e.g. after
--     R3 substitutes it in) and still be projectable later, exactly what
--     R5's own construction (fst\/snd of a freshly bound continuation
--     argument) relies on.
module OpSem where

import Data.Monoid (Sum (..))

-- ---------------------------------------------------------------------
-- Domains.agda's Ground\/⟦_⟧ᴳ, as runtime values instead of a GTy universe:
-- base constants, the distinguished loss type, unit, and pairs of ground
-- values (everything @PrimFun@\/@Op@ can consume or produce).
-- ---------------------------------------------------------------------

data Ground base r
  = GBase base
  | GLoss r
  | GUnit
  | GProd (Ground base r) (Ground base r)
  deriving (Eq, Show)

type PrimFun base r = Ground base r -> Ground base r

-- ---------------------------------------------------------------------
-- Syntax.agda's Val \/ LC \/ Handler \/ _⊢_!_, with Ty\/EffCxt erased and
-- Γ∋σ realised as a bare de Bruijn index (0 = innermost).
-- ---------------------------------------------------------------------

data Val eff base r op
  = VVar Int
  | VGnd (Ground base r)
  | VPair (Val eff base r op) (Val eff base r op)
  | VAbs (Expr eff base r op)

-- | A loss continuation g : σ → loss ! ε (Syntax.agda's @LC@) is just
-- another function-typed value; kept as a synonym purely for documentation.
type LC eff base r op = Val eff base r op

-- | Syntax.agda's @Handler@ record, evaluated already down to Haskell-level
-- functions from an operation identifier to its clause body (@clause@) and
-- the return-clause body (@ret@). @hLabel@ realises the ℓ index Handler
-- carries in Agda; @op :: op@ values elsewhere are compared against it via
-- 'OpLabel' to realise ℓ∈ε\/Handles-style dispatch without EffCxt.
data Handler eff base r op = Handler
  { hLabel  :: eff,
    -- | Context Γ,par,out,fl,fk ⊢ σ'!ε (par outermost\/highest index, fk
    -- innermost\/index 0) -- see 'substMulti' at each call site for the
    -- exact binding order this expects.
    hClause :: op -> Expr eff base r op,
    -- | Context Γ,par,σ ⊢ σ'!ε (σ innermost\/index 0).
    hRet    :: Expr eff base r op
  }

-- | Syntax.agda's core expressions Γ ⊢ σ ! ε. @sub@\/@sub1@\/@sub2@
-- inclusion witnesses on THEN\/GLOCAL are dropped: they are pure typing
-- evidence, never consulted by any reduction rule.
data Expr eff base r op
  = EVal (Val eff base r op)
  | EFun (PrimFun base r) (Expr eff base r op)
  | EPair (Expr eff base r op) (Expr eff base r op)
  | EFst (Expr eff base r op)
  | ESnd (Expr eff base r op)
  | EApp (Expr eff base r op) (Expr eff base r op)
  | EOp op (Expr eff base r op)
  | ELoss (Expr eff base r op)
  | EThen (Expr eff base r op) (LC eff base r op)
  | EGlocal (Expr eff base r op) (LC eff base r op)
  | EReset (Expr eff base r op)
  | EHandle (Handler eff base r op) (Expr eff base r op) (Expr eff base r op)

isValueE :: Expr eff base r op -> Bool
isValueE (EVal _) = True
isValueE _        = False

-- | Partial: only ever called once 'isValueE' has been checked.
asValue :: Expr eff base r op -> Val eff base r op
asValue (EVal v) = v
asValue _        = error "OpSem.asValue: not a value"

-- ---------------------------------------------------------------------
-- Subst.agda: renaming\/substitution, ported with Ren\/Sub both realised
-- as index-indexed functions (@Sub Γ Γ' = ∀σ. Γ∋σ → Val Γ' σ@ becomes
-- @Int -> Val ...@; a plain renaming is just @VVar . ρ@ composed in, so a
-- separate Ren type isn't needed).
-- ---------------------------------------------------------------------

type Sub eff base r op = Int -> Val eff base r op

idSub :: Sub eff base r op
idSub = VVar

cons :: Val eff base r op -> Sub eff base r op -> Sub eff base r op
cons v _ 0 = v
cons _ s n = s (n - 1)

wkSub :: Sub eff base r op
wkSub = VVar . (+ 1)

extS :: Sub eff base r op -> Sub eff base r op
extS _ 0 = VVar 0
extS s n = shiftVal 1 (s (n - 1))

subV :: Sub eff base r op -> Val eff base r op -> Val eff base r op
subV s (VVar i)    = s i
subV _ (VGnd g)    = VGnd g
subV s (VPair v w) = VPair (subV s v) (subV s w)
subV s (VAbs e)    = VAbs (subE (extS s) e)

subE :: Sub eff base r op -> Expr eff base r op -> Expr eff base r op
subE s (EVal v)           = EVal (subV s v)
subE s (EFun f e)         = EFun f (subE s e)
subE s (EPair e1 e2)      = EPair (subE s e1) (subE s e2)
subE s (EFst e)           = EFst (subE s e)
subE s (ESnd e)           = ESnd (subE s e)
subE s (EApp e1 e2)       = EApp (subE s e1) (subE s e2)
subE s (EOp o e)          = EOp o (subE s e)
subE s (ELoss e)          = ELoss (subE s e)
subE s (EThen e g)        = EThen (subE s e) (subV s g)
subE s (EGlocal e g)      = EGlocal (subE s e) (subV s g)
subE s (EReset e)         = EReset (subE s e)
subE s (EHandle h e1 e2)  = EHandle (subH s h) (subE s e1) (subE s e2)

subH :: Sub eff base r op -> Handler eff base r op -> Handler eff base r op
subH s h =
  Handler
    { hLabel = hLabel h,
      hClause = \op -> subE (extS (extS (extS (extS s)))) (hClause h op),
      hRet = subE (extS (extS s)) (hRet h)
    }

shiftVal :: Int -> Val eff base r op -> Val eff base r op
shiftVal d = subV (VVar . (+ d))

shiftExpr :: Int -> Expr eff base r op -> Expr eff base r op
shiftExpr d = subE (VVar . (+ d))

weaken1V :: Val eff base r op -> Val eff base r op
weaken1V = shiftVal 1

weaken1 :: Expr eff base r op -> Expr eff base r op
weaken1 = shiftExpr 1

weaken1H :: Handler eff base r op -> Handler eff base r op
weaken1H = subH wkSub

-- | e[v] (Subst.agda's @_[_]@): substitute the innermost bound variable.
subst1 :: Val eff base r op -> Expr eff base r op -> Expr eff base r op
subst1 v = subE (cons v idSub)

-- | Sequential single-substitution of a list of values, innermost-bound
-- variable first -- realises Subst.agda's nested @cons v1 (cons v2 ...)@
-- simultaneous substitutions (see the module header\/call sites for why
-- this coincides with them: none of the substituted values ever refer to
-- each other's freshly-bound slot).
substMulti :: [Val eff base r op] -> Expr eff base r op -> Expr eff base r op
substMulti []       e = e
substMulti (v : vs) e = substMulti vs (subst1 v e)

-- | v_r(v,x) : (Γ,σ) ⊢ σ'!ε (OpSem.agda's @retApplied@): ret's own @par@
-- slot fixed to (weakened) v, its @σ@ slot left as the fresh bound var.
retApplied :: Handler eff base r op -> Val eff base r op -> Expr eff base r op
retApplied h v = subE (cons (VVar 0) (cons (weaken1V v) wkSub)) (hRet h)

-- | The zero loss continuation λ^ε x:σ.0.
zeroLC :: Monoid r => LC eff base r op
zeroLC = VAbs (EVal (VGnd (GLoss mempty)))

-- ---------------------------------------------------------------------
-- Fig. 5's Frame\/SFrame\/ContCxt, with all four type indices erased.
-- Only used for rule R5's own delimited-continuation capture (matchR5
-- below): ordinary congruence (F-rule\/S1-S4) is realised directly inside
-- 'step' by structural recursion instead, since it never needs to inspect
-- or replay a *captured* context the way R5 does.
-- ---------------------------------------------------------------------

data KFrame eff base r op
  = KFun (PrimFun base r)
  | KPairL (Expr eff base r op)
  | KPairR (Val eff base r op)
  | KFst
  | KSnd
  | KAppL (Expr eff base r op)
  | KAppR (Val eff base r op)
  | KOp op
  | KLoss
  | KHandleP (Handler eff base r op) (Expr eff base r op)
  | KHandleB (Handler eff base r op) (Val eff base r op)
  | KThen (LC eff base r op)
  | KGlocal (LC eff base r op)
  | KReset

-- | ContCxt, built outside-in with the hole innermost: index 0 is the
-- frame *closest* to the hole (mirrors Agda's @F∘@\/@S∘@ nesting, see
-- 'plugK').
type Kont eff base r op = [KFrame eff base r op]

plugKFrame :: KFrame eff base r op -> Expr eff base r op -> Expr eff base r op
plugKFrame (KFun f)       e = EFun f e
plugKFrame (KPairL e2)    e = EPair e e2
plugKFrame (KPairR v)     e = EPair (EVal v) e
plugKFrame KFst           e = EFst e
plugKFrame KSnd           e = ESnd e
plugKFrame (KAppL e2)     e = EApp e e2
plugKFrame (KAppR v)      e = EApp (EVal v) e
plugKFrame (KOp o)        e = EOp o e
plugKFrame KLoss          e = ELoss e
plugKFrame (KHandleP h b) e = EHandle h e b
plugKFrame (KHandleB h v) e = EHandle h (EVal v) e
plugKFrame (KThen g1)     e = EThen e g1
plugKFrame (KGlocal g1)   e = EGlocal e g1
plugKFrame KReset         e = EReset e

plugK :: Kont eff base r op -> Expr eff base r op -> Expr eff base r op
plugK []       e = e
plugK (f : fs) e = plugK fs (plugKFrame f e)

weakenKFrame :: KFrame eff base r op -> KFrame eff base r op
weakenKFrame (KFun f)       = KFun f
weakenKFrame (KPairL e)     = KPairL (weaken1 e)
weakenKFrame (KPairR v)     = KPairR (weaken1V v)
weakenKFrame KFst           = KFst
weakenKFrame KSnd           = KSnd
weakenKFrame (KAppL e)      = KAppL (weaken1 e)
weakenKFrame (KAppR v)      = KAppR (weaken1V v)
weakenKFrame (KOp o)        = KOp o
weakenKFrame KLoss          = KLoss
weakenKFrame (KHandleP h b) = KHandleP (weaken1H h) (weaken1 b)
weakenKFrame (KHandleB h v) = KHandleB (weaken1H h) (weaken1V v)
weakenKFrame (KThen g1)     = KThen (weaken1V g1)
weakenKFrame (KGlocal g1)   = KGlocal (weaken1V g1)
weakenKFrame KReset         = KReset

-- | weaken1K.
weakenK :: Kont eff base r op -> Kont eff base r op
weakenK = map weakenKFrame

-- ---------------------------------------------------------------------
-- Rule R5's own search: "is the (unique, CBV) active redex inside this
-- handler body an operation call for MY OWN label ℓ, reachable without
-- crossing another handler for ℓ along the way (¬ Handles k ℓ)?" This
-- walks the exact same shape every Frame\/SFrame allows (mirroring
-- ContCxt\/plugK's own grammar), stopping either at a same-label 'EOp'
-- (success) or at any node whose *own* base rule would fire instead
-- (failure -- that redex belongs to ordinary 'step', via S1, not R5).
--
-- The recursive descent through a same-label 'EHandle' deliberately fails
-- (rather than continuing inward): that inner handler shadows the outer
-- one, and its own R5\/R6\/S1 -- tried the next time 'step' looks at it --
-- resolves the call instead, exactly as ¬ Handles k ℓ requires of k.
-- ---------------------------------------------------------------------

matchR5 ::
  Eq eff =>
  (op -> eff) ->
  eff ->
  Expr eff base r op ->
  Maybe (Kont eff base r op, op, Val eff base r op)
matchR5 opLabel target = go
  where
    wrap kf = fmap (\(k, o, v) -> (k ++ [kf], o, v))

    go (EVal _) = Nothing
    go (EFun f e)
      | not (isValueE e) = wrap (KFun f) (go e)
      | otherwise = Nothing
    go (EPair e1 e2)
      | not (isValueE e1) = wrap (KPairL e2) (go e1)
      | not (isValueE e2) = wrap (KPairR (asValue e1)) (go e2)
      | otherwise = Nothing
    go (EFst e) = wrap KFst (go e)
    go (ESnd e) = wrap KSnd (go e)
    go (EApp e1 e2)
      | not (isValueE e1) = wrap (KAppL e2) (go e1)
      | not (isValueE e2) = wrap (KAppR (asValue e1)) (go e2)
      | otherwise = Nothing
    go (EOp o e)
      | not (isValueE e) = wrap (KOp o) (go e)
      | opLabel o == target = Just ([], o, asValue e)
      | otherwise = Nothing
    go (ELoss e)
      | not (isValueE e) = wrap KLoss (go e)
      | otherwise = Nothing
    go (EThen e g1)
      | not (isValueE e) = wrap (KThen g1) (go e)
      | otherwise = Nothing
    go (EGlocal e g1)
      | not (isValueE e) = wrap (KGlocal g1) (go e)
      | otherwise = Nothing
    go (EReset e)
      | not (isValueE e) = wrap KReset (go e)
      | otherwise = Nothing
    go (EHandle h pe be)
      | not (isValueE pe) = wrap (KHandleP h be) (go pe)
      | hLabel h == target = Nothing
      | not (isValueE be) = wrap (KHandleB h (asValue pe)) (go be)
      | otherwise = Nothing

-- ---------------------------------------------------------------------
-- Fig. 6\/11: the small-step judgment g ⊢ e -[r]-> e'. One recursive
-- function per Expr former, each implementing exactly the base rule(s)
-- named in its comment when its principal subexpression(s) are already
-- values, and otherwise recursing via the matching congruence rule
-- (F-rule for the "regular frame" formers, S1-S4 for THEN\/GLOCAL\/RESET\/
-- HANDLE's own body).
--
-- 'fRuleG' realises F-rule's own continuation-rebuilding formula
-- @g' = vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g))@:
-- given @replug@ = "plug a hole value back into the CURRENT (weakened)
-- frame", it builds exactly that g'. It is used ONLY to derive the
-- ambient continuation for the recursive hypothesis -- the step's own
-- conclusion always re-wraps with the ORIGINAL (unweakened) frame, per
-- F-rule's own statement.
-- ---------------------------------------------------------------------

fRuleG ::
  Monoid r =>
  (Expr eff base r op -> Expr eff base r op) ->
  LC eff base r op ->
  LC eff base r op
fRuleG replug g = VAbs (EThen (replug (EVal (VVar 0))) (weaken1V g))

step ::
  (Eq eff, Monoid r) =>
  (op -> eff) ->
  LC eff base r op ->
  Expr eff base r op ->
  Maybe (r, Expr eff base r op)
step opLabel g expr = case expr of
  EVal _ -> Nothing
  -- R1, F-fun.
  EFun f e
    | EVal (VGnd gv) <- e -> Just (mempty, EVal (VGnd (f gv)))
    | not (isValueE e) -> do
        (r, e') <- step opLabel (fRuleG (EFun f) g) e
        return (r, EFun f e')
    | otherwise -> Nothing
  -- R2-pair, F-pairL\/F-pairR.
  EPair e1 e2
    | not (isValueE e1) -> do
        (r, e1') <- step opLabel (fRuleG (\h -> EPair h (weaken1 e2)) g) e1
        return (r, EPair e1' e2)
    | not (isValueE e2) ->
        let v1 = asValue e1
         in do
              (r, e2') <- step opLabel (fRuleG (\h -> EPair (EVal (weaken1V v1)) h) g) e2
              return (r, EPair e1 e2')
    | otherwise -> Just (mempty, EVal (VPair (asValue e1) (asValue e2)))
  -- R2-fst, F-fst.
  EFst e
    | EVal (VPair v _) <- e -> Just (mempty, EVal v)
    | otherwise -> do
        (r, e') <- step opLabel (fRuleG EFst g) e
        return (r, EFst e')
  -- R2-snd, F-snd.
  ESnd e
    | EVal (VPair _ w) <- e -> Just (mempty, EVal w)
    | otherwise -> do
        (r, e') <- step opLabel (fRuleG ESnd g) e
        return (r, ESnd e')
  -- R3, F-appL\/F-appR.
  EApp e1 e2
    | not (isValueE e1) -> do
        (r, e1') <- step opLabel (fRuleG (\h -> EApp h (weaken1 e2)) g) e1
        return (r, EApp e1' e2)
    | not (isValueE e2) ->
        let v1 = asValue e1
         in do
              (r, e2') <- step opLabel (fRuleG (\h -> EApp (EVal (weaken1V v1)) h) g) e2
              return (r, EApp e1 e2')
    | EVal (VAbs body) <- e1, EVal v <- e2 -> Just (mempty, subst1 v body)
    | otherwise -> Nothing
  -- F-op; the value case (op ∉ any enclosing handler reached so far) is
  -- only ever resolved from the *outside*, by an enclosing EHandle's own
  -- 'matchR5' -- reached directly here, it is genuinely stuck.
  EOp o e
    | not (isValueE e) -> do
        (r, e') <- step opLabel (fRuleG (EOp o) g) e
        return (r, EOp o e')
    | otherwise -> Nothing
  -- R4, F-loss.
  ELoss e
    | EVal (VGnd (GLoss rv)) <- e -> Just (rv, EVal (VGnd GUnit))
    | not (isValueE e) -> do
        (r, e') <- step opLabel (fRuleG ELoss g) e
        return (r, ELoss e')
    | otherwise -> Nothing
  -- R7 (base case), S2 (congruence: steps e under g1, NOT the ambient g;
  -- the resulting r is deferred into a fresh loss(r) ▶ ... rather than
  -- propagated directly, exactly mirroring OpSem.agda's own encoding).
  EThen e g1
    | EVal v <- e, VAbs body <- g1 -> Just (mempty, EGlocal (subst1 v body) zeroLC)
    | not (isValueE e) -> do
        (r, e') <- step opLabel g1 e
        return (mempty, EThen (ELoss (EVal (VGnd (GLoss r)))) (VAbs (weaken1 (EThen e' g1))))
    | otherwise -> Nothing
  -- R8 (base case), S3 (congruence: steps e under g1, r propagates directly).
  EGlocal e g1
    | EVal v <- e -> Just (mempty, EVal v)
    | otherwise -> do
        (r, e') <- step opLabel g1 e
        return (r, EGlocal e' g1)
  -- R9, S4 (congruence under the SAME ambient g, own loss discarded --
  -- this is exactly what makes reset a censor).
  EReset e
    | EVal v <- e -> Just (mempty, EVal v)
    | otherwise -> do
        (_, e') <- step opLabel g e
        return (mempty, EReset e')
  -- F-handleP (parameter not yet a value), R6\/R5\/S1 (parameter is a
  -- value v1: return clause if the body already is too, else try R5's
  -- direct dispatch via 'matchR5', else S1 congruence under the
  -- return-clause-switched continuation).
  EHandle h paramE bodyE
    | not (isValueE paramE) -> do
        let replug hole = EHandle (weaken1H h) hole (weaken1 bodyE)
        (r, paramE') <- step opLabel (fRuleG replug g) paramE
        return (r, EHandle h paramE' bodyE)
    | EVal v2 <- bodyE ->
        let v1 = asValue paramE
         in Just (mempty, substMulti [v2, v1] (hRet h))
    | otherwise ->
        let v1 = asValue paramE
         in case matchR5 opLabel (hLabel h) bodyE of
              Just (kInner, opW, v2) ->
                let kOuter = weakenK kInner
                    h' = weaken1H h
                    g'' = weaken1V g
                    handled = EHandle h' (EFst (EVal (VVar 0))) (plugK kOuter (ESnd (EVal (VVar 0))))
                    fk = VAbs (EGlocal handled zeroLC)
                    fl = VAbs (EThen handled g'')
                 in Just (mempty, substMulti [fk, fl, v2, v1] (hClause h opW))
              Nothing ->
                let g' = VAbs (EThen (retApplied h v1) (weaken1V g))
                 in do
                      (r, bodyE') <- step opLabel g' bodyE
                      return (r, EHandle h paramE bodyE')

-- ---------------------------------------------------------------------
-- Fig. 7: the big-step judgment g ⊢ e ⇒[r] w, driven by a SINGLE fixed
-- ambient continuation across the whole run (matching OpSem.agda's own
-- @step@ big-step constructor, which reuses the very same @g@ for both
-- the small step and the recursive continuation) -- @g@ only ever varies
-- *within* one 'step' call's own recursive descent, never across
-- successive top-level steps. 'run' uses the canonical zero continuation
-- γ₀, matching SelectionMonadHat.hs's own top-level driver.
-- ---------------------------------------------------------------------

run ::
  (Eq eff, Monoid r) =>
  (op -> eff) ->
  Expr eff base r op ->
  (Expr eff base r op, r)
run opLabel = go mempty
  where
    go acc e = case step opLabel zeroLC e of
      Nothing -> (e, acc)
      Just (r, e') -> go (acc <> r) e'

-- | Run for a fixed number of steps, for inspecting a reduction sequence
-- (e.g. in GHCi) rather than only its final result.
trace :: (Eq eff, Monoid r) => (op -> eff) -> Int -> Expr eff base r op -> [Expr eff base r op]
trace _ 0 e = [e]
trace opLabel n e = e : case step opLabel zeroLC e of
  Nothing -> []
  Just (_, e') -> trace opLabel (n - 1) e'

---------------------------
-- Examples
--
-- Hand-written raw AST (there is no surface-syntax parser here), so kept
-- deliberately small: enough to exercise loss (R4), an ordinary
-- application (R3), and -- separately -- a handler dispatch (R5\/R6) to
-- see in practice what the module header's fst\/snd fidelity note predicts.
---------------------------

data Eff = NDetEff deriving (Eq, Show)

data Op = Decide deriving (Eq, Show)

exampleOpLabel :: Op -> Eff
exampleOpLabel Decide = NDetEff

data Base = BBool Bool deriving (Eq, Show)

type R = Sum Int

type V = Val Eff Base R Op

type E = Expr Eff Base R Op

gLoss :: R -> V
gLoss = VGnd . GLoss

gBool :: Bool -> V
gBool = VGnd . GBase . BBool

-- | Pure example, no handlers: (\_ -> ()) (loss 3) -- record a loss of 3,
-- discard the resulting unit, finish with (). Exercises R4 (loss), R3
-- (beta), F-rule congruence (evaluating loss under the application's
-- argument position) and the big-step driver.
lossExample :: E
lossExample =
  EApp (EVal (VAbs (EVal (VGnd GUnit)))) (ELoss (EVal (gLoss (Sum 3))))

-- | A trivial "always choose True" non-determinism handler: hRet is the
-- identity on the handled value, hClause ignores its own choice
-- continuation (fl) entirely and just resumes the delimited continuation
-- (fk) with (par, True). Context for hClause is Γ,par,out,fl,fk with fk
-- at index 0 (innermost) -- see 'substMulti'\/'hClause' docs above.
hAlwaysTrue :: Handler Eff Base R Op
hAlwaysTrue =
  Handler
    { hLabel = NDetEff,
      hRet = EVal (VVar 0),
      hClause = \op -> case op of
        Decide ->
          EApp (EVal (VVar 0)) (EVal (VPair (VVar 3) (gBool True)))
    }

-- | handle hAlwaysTrue (with param ()) (decide ()) -- directly dispatches
-- via R5 (the op call IS the handler's whole body, so 'matchR5' fires
-- with an empty captured continuation). Exercises R5\/R6 and, via
-- hClause's own use of fk, R5's own pArg\/yArg (fst\/snd of the freshly
-- substituted tuple z, now a genuine value-level 'VPair' once fk is
-- applied -- exactly what the R2-pair coalescing rule makes projectable).
decideExample :: E
decideExample =
  EHandle hAlwaysTrue (EVal (VGnd GUnit)) (EOp Decide (EVal (VGnd GUnit)))
