> {
> -----------------------------------------------------------------------------
> -- |
> -- Module      :  H.Parser
> -- Copyright   :  (c) Simon Marlow, Sven Panne 1997-2000
> --                (c) Iago Abal, 2011
> -- License     :  BSD-style (see the file libraries/base/LICENSE)
> --
> -- Maintainer  :  iago.abal@gmail.com
> -- Stability   :  experimental
> -- Portability :  portable
> --
> -- H! parser.
> --
> -----------------------------------------------------------------------------
>
> module H.Parser (
>   parseModule, parseModuleWithMode,
>   ParseMode(..), defaultParseMode, ParseResult(..),
>   parseH) where
> 
> import H.Monad ( H )
> import H.Syntax
> import H.SrcLoc
> import Pretty
> import H.Phase
> import H.Parser.ParseMonad
> import H.Parser.Lexer
> import H.Parser.Utils
> import H.Parser.Fixity
>
> import Name
> import Sorted
>
> import Control.Monad ( (>=>) )
> import Control.Monad.Error ( throwError )
> }


-----------------------------------------------------------------------------
Conflicts: 2 shift/reduce

2 for ambiguity in 'case x of y | let z = y in z :: Bool -> b'
  (don't know whether to reduce 'Bool' as a btype or shift the '->'.
   Similarly lambda and if.  The default resolution in favour of the
   shift means that a guard can never end with a type signature.
   In mitigation: it's a rare case and no Haskell implementation
   allows these, because it would require unbounded lookahead.)
  There are 2 conflicts rather than one because contexts are parsed
  as btypes (cf ctype).

-----------------------------------------------------------------------------


> %token
> VARID  { VarId $$ }
> CONID  { ConId $$ }
> INT    { IntTok $$ }

Symbols

> '(' { LeftParen }
> ')' { RightParen }
> ';' { SemiColon }
> '{' { LeftCurly }
> '}' { RightCurly }
> vccurly { VRightCurly }     -- a virtual close brace
> '[' { LeftSquare }
> ']' { RightSquare }
> ',' { Comma }
> '_' { Underscore }

Reserved operators

> '.'   { Dot }
> '..'  { DotDot }
> ':'   { Colon }
> '::'  { DoubleColon }
> '='   { Equals }
> '\\'  { Backslash }
> '|'   { Bar }
> '->'  { RightArrow }
> '@'   { At }
> '~'   { Tilde }
> '||'  { BarBar }
> '&&'  { AmpAmp }
> '==>' { Implication }
> '<=>' { Iff }
> '+'   { Plus }
> '-'   { Minus }
> '*'   { Asterisk }
> '/'   { Slash }
> '%'   { Percent }
> '^'   { Caret }
> '=='  { EqEq }
> '/='  { SlashEq }
> '<'   { Lt }
> '<='  { LtEq }
> '>'   { Gt }
> '>='  { GtEq }

Reserved Ids

> 'Bool'    { KW_Bool }
> 'False'   { KW_False }
> 'Int'     { KW_Int }
> 'Nat'     { KW_Nat }
> 'True'    { KW_True }
> 'case'    { KW_Case }
> 'data'    { KW_Data }
> 'else'    { KW_Else }
> 'exists'  { KW_Exists }
> 'forall'  { KW_Forall }
> 'if'      { KW_If }
> 'in'      { KW_In }
> 'lemma'   { KW_Lemma }
> 'let'     { KW_Let }
> 'module'  { KW_Module }
> 'of'      { KW_Of }
> 'theorem' { KW_Theorem }
> 'then'    { KW_Then }
> 'type'    { KW_Type }
> 'where'   { KW_Where }



> %monad { P }
> %lexer { lexer } { EOF }
> %name parse
> %tokentype { Token }
> %%

-----------------------------------------------------------------------
Module Header

> module :: { Module Pr }
> : srcloc 'module' modid 'where' body    { Module $1 $3 $5 }

> body :: { [Decl Pr] }
> : '{'  bodyaux '}'      { $2 }
> | open bodyaux close    { $2 }

> bodyaux :: { [Decl Pr] }
> : optsemis topdecls { $2 }
> | optsemis          { [] }

> semis :: { () }
> : optsemis ';'        { () }

> optsemis :: { () }
> : semis         { () }
> | {- empty -}       { () }

-----------------------------------------------------------------------
Top-Level Declarations

Note: The report allows topdecls to be empty. This would result in another
shift/reduce-conflict, so we don't handle this case here, but in bodyaux.

> topdecls :: { [Decl Pr] }
> : topdecls1 optsemis    {% do { decls <- groupDeclsBinds $1
>                               ; checkDupDecls decls
>                               ; return decls }
>                         }

> topdecls1 :: { [Decl Pr] }
> : topdecls1 semis topdecl   { $1 ++ [$3] }
> | topdecl                   { [$1] }

> topdecl :: { Decl Pr }
> : srcloc 'type' tyconid typarams '=' type     { TypeDecl $1 $3 $4 $6 }
> | srcloc 'data' tyconid typarams '=' constrs  { DataDecl $1 $3 $4 $6 }
> | valdecl                                   { $1 }
> | srcloc goaltype goalname '=' exp          { GoalDecl $1 $2 $3 NoPostTc $5 }

> goaltype :: { GoalType }
> : 'theorem' { TheoremGoal }
> | 'lemma'   { LemmaGoal }

> valdecls :: { [Decl Pr] }
> : optsemis valdecls1 optsemis  {% do { decls <- groupDeclsBinds $2
>                                      ; checkDupDecls decls
>                                      ; return decls }
>                                }
> | optsemis      { [] }

> valdecls1 :: { [Decl Pr] }
> : valdecls1 semis valdecl   { $1 ++ [$3] }
> | valdecl        { [$1] }

> valdecl :: { Decl Pr }
> : bind      { ValDecl $1 }

  > : signdecl      { $1 }

> valdecllist :: { [Decl Pr] }
> : '{'  valdecls '}'    { $2 }
> | open valdecls close    { $2 }

  > signdecl :: { FnDecl Pr }
  > : srcloc vars ':' polytype { TypeSig $1 $2 $4 }

> vars  :: { [VAR Pr] }
> : vars ',' var      { $1 ++ [$3] }
> | var               { [$1] }

----------------------------------------------------------------------
Types

> type :: { Tau Pr }
> : btype '->' type   { mkFunTy $1 $3 }
> | btype       { $1 }

> btype :: { Tau Pr }
> : btype atype     { AppTyIn $1 $2 }
> | atype       { $1 }

> atype :: { Tau Pr }
> : gtycon            { ConTyIn $1 }
> | tyvar             { VarTy $1 }
> | '(' tuptypes ')'   { TupleTy $2 }
> | '[' type ']'      { ListTy $2 }
> | '(' type ')'      { $2 }
> | '{' apat ':' type '}'           { PredTy $2 $4 Nothing }
> | '{' apat ':' type '|' prop '}'  { PredTy $2 $4 (Just $6) }

> gtycon :: { TyCON Pr }
> : '(' ')'     { unitTyName }
> | 'Int'       { intTyName }
> | 'Nat'       { natTyName }
> | 'Bool'      { boolTyName }
> |  utycon     { $1 }


> polytype :: { Sigma Pr }
> : 'forall' typarams '.' type  { ForallTy $2 $4 }
> | type                        { tau2sigma $1 }


> tuptypes :: { [Dom Pr] }
> : tuptypes ',' tupdom   { $1 ++ [$3] }
> | tupdom  ',' tupdom    { [$1,$3] }

> tupdom :: { Dom Pr }
> : type   { Dom Nothing $1 Nothing }
> | apat ':' type { Dom (Just $1) $3 Nothing }
> | apat ':' type '|' prop { Dom (Just $1) $3 (Just $5) }

> typarams :: { TyParams Pr }
> : typarams typaram  { $1 ++ [$2] }
> | {- empty -}       { [] }

> typaram :: { TyVAR Pr }
> : tyvar     { $1 }


-----------------------------------------------------------------------------
Datatype declarations

> constrs :: { [ConDecl Pr] }
> : constrs '|' constr    { $1 ++ [$3] }
> | constr      { [$1] }

> constr :: { ConDecl Pr }
> : srcloc conid atypes   { ConDeclIn $1 $2 $3 }

-- : srcloc scontype    { ConDecl $1 (fst $2) (snd $2) }

> atypes :: { [Tau Pr] }
> : atypes atype   { $1 ++ [$2] }
> | {- empty -} { [] }

  > scontype :: { (TyNAME Pr, [Tau Pr]) }
  > : btype       {% do { (c,ts) <- splitTyConApp $1;
  >                       return (c,ts) } }

-----------------------------------------------------------------------------
Value definitions

> bind :: { Bind Pr }
> : funsig semis funbind            {% funWithSig $1 $3 }
> | funbind                         { $1 }
> | srcloc pat rhs wherebinds       { PatBind (Just $1) $2 (Rhs NoPostTc $3 $4) }

> funsig :: { (SrcLoc,NAME Pr,Sigma Pr) }
> : srcloc varid ':' polytype { ($1,$2,$4) }

> funbind :: { Bind Pr }
> : srcloc varid apats rhs wherebinds
>         { FunBind Rec $2 NoTypeSig NoPostTc [Match (Just $1) $3 (Rhs NoPostTc $4 $5)] }
> | srcloc varid rhs wherebinds
>         { FunBind Rec $2 NoTypeSig NoPostTc [Match (Just $1) [] (Rhs NoPostTc $3 $4)] }

> binds :: { [Bind Pr] }
> : valdecllist     { getParsedBinds $1 }

> wherebinds :: { WhereBinds Pr }
> : 'where' binds    { $2 }
> | {- empty -}     { [] }

> rhs :: { GRhs Pr }
> : '=' exp     { UnGuarded $2 }
> | gdrhs       { Guarded (GuardedRhssIn  $1) }

> gdrhs :: { [GuardedRhs Pr] }
> : gdrhs gdrh      { $1 ++ [$2] }
> | gdrh        { [$1] }

> gdrh :: { GuardedRhs Pr }
> : srcloc '|' guard '=' exp { GuardedRhs $1 $3 $5 }

-----------------------------------------------------------------------------
Expressions

Note: The Report specifies a meta-rule for lambda, let and if expressions
(the exp's that end with a subordinate exp): they extend as far to
the right as possible.  That means they cannot be followed by a type
signature or infix application.  To implement this without shift/reduce
conflicts, we split exp10 into these expressions (exp10a) and the others
(exp10b).  That also means that only an exp0 ending in an exp10b (an exp0b)
can followed by a type signature or infix application.  So we duplicate
the exp0 productions to distinguish these from the others (exp0a).

> prop :: { Prop Pr }
> : exp { $1 }

> guard :: { Prop Pr }
> : 'else'      { ElseGuard }
> | exp0        { $1 }

> exp   :: { Exp Pr }
> : exp0b ':' srcloc polytype   { Coerc $3 $1 $4 }
> | exp0        { $1 }

> exp0 :: { Exp Pr }
> : exp0a       { $1 }
> | exp0b       { $1 }

> exp0a :: { Exp Pr }
> : exp0b op exp10a   { InfixApp $1 (Op $2) $3 }
> | exp10a      { $1 }

> exp0b :: { Exp Pr }
> : exp0b op exp10b   { InfixApp $1 (Op $2) $3 }
> | exp10b      { $1 }

> exp10a :: { Exp Pr }
> : '\\' srcloc apats '->' exp  { Lam (Just $2) $3 (Rhs NoPostTc (UnGuarded $5) []) }
> | 'let' binds 'in' exp { Let $2 $4 }
> | 'if' exp 'then' exp 'else' exp { Ite NoPostTc $2 $4 $6 }
> | 'if' gdpats    { If NoPostTc (GuardedRhssIn $2) }
> | quantifier qvars ',' exp  { QP $1 $2 $4 }

> quantifier :: { Quantifier }
> : 'exists'  { ExistsQ }
> | 'forall'  { ForallQ }

> exp10b :: { Exp Pr }
> : 'case' exp 'of' altslist  { Case $2 NoPostTc $4 }
> | '~' fexp      { PrefixApp (Op notOp) $2 }
> | '-' fexp      { PrefixApp (Op negOp) $2 }
> | fexp        { $1 }

> fexp :: { Exp Pr }
> : fexp aexp     { App $1 $2 }
> | aexp        { $1 }

> aexp  :: { Exp Pr }
> : aexp1       { $1 }

Note: The first two alternatives of aexp1 are not necessarily record
updates: they could be labeled constructions.

> aexp1 :: { Exp Pr }
> : aexp2       { $1 }

According to the Report, the left section (e op) is legal iff (e op x)
parses equivalently to ((e) op x).  Thus e must be an exp0b.

> aexp2 :: { Exp Pr }
> : var       { Var $1 }
> | gcon        { $1 }
> | literal     { Lit $1 }
> | '(' exp ')'     { Paren $2 }
> | '(' op ')'      { Op $2 }
> | '(' texps ')'     { Tuple NoPostTc $2 }
> | '[' list ']'         { $2 }
> | '(' exp0b op ')'    { LeftSection $2 (Op $3)  }
> | '(' op exp0 ')'   { RightSection (Op $2) $3 }

  > commas :: { Int }
  > : commas ','      { $1 + 1 }
  > | ','       { 1 }

> texps :: { [Exp Pr] }
> : texps ',' exp     { $1 ++ [$3] }
> | exp ',' exp     { [$1,$3] }


> apats :: { [Pat Pr] }
> : apats apat      { $1 ++ [$2] }
> | apat        { [$1] }


> pat   :: { Pat Pr }
> : pat1        { $1 }

  > : pat1 ':' type   { SigPat $1 $3 }

> pat1 :: { Pat Pr }
> : fpat '::' pat1    { InfixCONSPat NoPostTc $1 $3 }
> | fpat      { $1 }

> fpat :: { Pat Pr }
> : con apats   { ConPat $1 NoPostTc $2 }
> | apat        { $1 }

> apat :: { Pat Pr }
> : var '@' apat  { AsPat $1 $3 }
> | apat1         { $1 }

> apat1 :: { Pat Pr }
> : var       { VarPat $1 }
> | con        { ConPat $1 NoPostTc [] }
> | literal     { LitPat $1 }

 > | '(' pat ':' type ')'     { SigPat $2 $4 }

> | '(' pat ')'     { ParenPat $2 }
> | '(' tpats ')'     { TuplePat $2 NoPostTc }
> | '[' lpats ']'     { ListPat $2 NoPostTc }
> | '_'             { WildPatIn }

> tpats :: { [Pat Pr] }
> : tpats ',' pat     { $1 ++ [$3] }
> | pat ',' pat     { [$1,$3] }

> lpats :: { [Pat Pr] }
> : lpats ',' pat     { $1 ++ [$3] }
> | pat             { [$1] }
> | {- empty -}     { [] }


> qvar :: { QVar Pr }
> : var                   { QVar $1 Nothing }
> | '(' var ':' type ')'  { QVar $2 (Just $4) }

> qvars :: { [QVar Pr] }
> : qvars qvar  { $1 ++ [$2] }
> | qvar        { [$1] }

-----------------------------------------------------------------------------
List expressions

The rules below are little bit contorted to keep lexps left-recursive while
avoiding another shift/reduce-conflict.

> list :: { Exp Pr }
> : exp       { List NoPostTc [$1] }
> | lexps       { List NoPostTc $1 }
> | exp '..' exp      { EnumFromTo $1 $3 }
> | exp ',' exp '..' exp    { EnumFromThenTo $1 $3 $5 }

> lexps :: { [Exp Pr] }
> : lexps ',' exp     { $1 ++ [$3] }
> | exp ',' exp     { [$1,$3] }

-----------------------------------------------------------------------------
Case alternatives

> altslist :: { [Alt Pr] }
> : '{'  alts '}'     { $2 }
> | open alts close   { $2 }

> alts :: { [Alt Pr] }
> : optsemis alts1 optsemis { $2 }

> alts1 :: { [Alt Pr] }
> : alts1 semis alt   { $1 ++ [$3] }
> | alt       { [$1] }

> alt :: { Alt Pr }
> : srcloc pat altrhs { Alt (Just $1) $2 (Rhs NoPostTc $3 []) }

> altrhs :: { GRhs Pr }
> : '->' exp      { UnGuarded $2 }
> | gdpats      { Guarded (GuardedRhssIn $1) }

> gdpats :: { [GuardedRhs Pr] }
> : gdpats gdpat      { $1 ++ [$2] }
> | gdpat       { [$1] }

> gdpat :: { GuardedRhs Pr }
> : srcloc '|' guard '->' exp  { GuardedRhs $1 $3 $5 }

-----------------------------------------------------------------------------
Variables, Constructors and Operators.

> gcon :: { Exp Pr }
> : '(' ')'   { Con unitCon }
> | 'False'   { Con falseCon }
> | 'True'    { Con trueCon }
> | '(' '::' ')' { Con consCon }
> | '[' ']'   { Con nilCon }
> | conid     { Con (UserCon $1) }

Constructors that may appear in a ConPat pattern

> con :: { Con Pr }
> : '(' ')'   { unitCon }
> | 'False'   { falseCon }
> | 'True'    { trueCon }
> | '[' ']'   { nilCon }
> | conid     { UserCon $1 }

> var   :: { VAR Pr }
> : varid     { $1 }

> op  :: { Op }
> : '::'      { CONSOp }
> | boolop    { $1 }
> | intop     { $1 }

> boolop  :: { Op }
> : '||' { orOp }
> | '&&' { andOp }
> | '==>' { impOp }
> | '<=>' { iffOp }
> | '=='      { eqOp }
> | '/=' { neqOp }
> | '<' { ltOp }
> | '<=' { leOp }
> | '>' { gtOp }
> | '>=' { geOp }

> intop  :: { Op }
> : '+' { addOp }
> | '-' { subOp }
> | '*' { mulOp }
> | '/' { divOp }
> | '%' { modOp }
> | '^' { expOp }




-----------------------------------------------------------------------------
Identifiers and Symbols

> varid :: { VAR Pr }
> : VARID     { mkOccName VarNS $1 }

> conid :: { VAR Pr }
> : CONID     { mkOccName ConNS $1 }

> tyvarid :: { VAR Pr }
> : VARID     { mkOccName TyVarNS $1 }

> tyconid :: { VAR Pr }
> : CONID     { mkOccName TyConNS $1 }

> goalname :: { GoalNAME Pr }
> : VARID     { mkOccName GoalNS $1 }

> literal :: { Lit }
> : INT     { IntLit $1 }

> srcloc :: { SrcLoc }  : {% getSrcLoc }
 
-----------------------------------------------------------------------------
Layout

> open  :: { () } : {% pushCurrentContext }

> close :: { () }
> : vccurly   { () } -- context popped in lexer.
> | error     {% popContext }

-----------------------------------------------------------------------------
Miscellaneous (mostly renamings)

> modid :: { ModuleName }
> : CONID     { ModName $1 }

> tyvar :: { TyVAR Pr }
> : VARID     { mkOccName TyVarNS $1 }

> utycon :: { TyCON Pr }
> : tyconid     { UserTyCon $1 }

-----------------------------------------------------------------------------

> {
> happyError :: P a
> happyError = fail "Parse error"

> instance (Pretty a) => Pretty (ParseResult a) where
>  pretty (ParseOk a) = pretty a
>  pretty (ParseFailed loc errmsg) = mySep [pretty loc <> char ':', text errmsg]

> -- | Parse of a string, which should contain a complete H! module.
> parseModule :: String -> ParseResult (Module Pr)
> parseModule = runParser parse >=> applyPreludeFixities

> -- | Parse of a string, which should contain a complete H! module.
> parseModuleWithMode :: ParseMode -> String -> ParseResult (Module Pr)
> parseModuleWithMode mode = runParserWithMode mode parse >=> applyPreludeFixities

> parseH :: ParseResult a -> H () () () a
> parseH (ParseOk a) = return a
> parseH (ParseFailed loc msg) = throwError $ mySep [pretty loc <> char ':', text msg]
> }
