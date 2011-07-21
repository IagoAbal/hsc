> {
> {-# LANGUAGE TypeOperators #-}
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
>		parseModule, parseModuleWithMode,
>		ParseMode(..), defaultParseMode, ParseResult(..)) where
> 
> import H.Syntax
> import H.Phase
> import H.ParseMonad
> import H.Lexer
> import H.ParseUtils
> import Name
> import Sorted
> }

ToDo: Check exactly which names must be qualified with Prelude (commas and friends)
ToDo: Inst (MPCs?)
ToDo: Polish constr a bit
ToDo: Ugly: exp0b is used for lhs, pat, exp0, ...
ToDo: Differentiate between record updates and labeled construction.

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
>	VARID 	 { VarId $$ }
>	CONID	 { ConId $$ }
>	INT	 { IntTok $$ }

Symbols

>	'('	{ LeftParen }
>	')'	{ RightParen }
>	';'	{ SemiColon }
>	'{'	{ LeftCurly }
>	'}'	{ RightCurly }
>	vccurly { VRightCurly }			-- a virtual close brace
>	'['	{ LeftSquare }
>	']'	{ RightSquare }
>  	','	{ Comma }
>	'_'	{ Underscore }

Reserved operators

>	'..'	{ DotDot }
>	':'	{ Colon }
>	'::'	{ DoubleColon }
>	'='	{ Equals }
>	'\\'	{ Backslash }
>	'|'	{ Bar }
>	'->'	{ RightArrow }
>	'@'	{ At }
>	'-'	{ Minus }
> '==' { OP_Eq }

Reserved Ids

>	'case'		{ KW_Case }
>	'data'		{ KW_Data }
>	'else'		{ KW_Else }
> 'exists'  { KW_Exists }
> 'forall'  { KW_Forall }
>	'if'		{ KW_If }
>	'in'		{ KW_In }
> 'lemma' { KW_Lemma }
>	'let'		{ KW_Let }
>	'module'	{ KW_Module }
>	'of'		{ KW_Of }
> 'theorem' { KW_Theorem }
>	'then'		{ KW_Then }
>	'type'		{ KW_Type }
>	'where'		{ KW_Where }

Special Ids


> %monad { P }
> %lexer { lexer } { EOF }
> %name parse
> %tokentype { Token }
> %%

-----------------------------------------------------------------------------
Module Header

> module :: { Module Pr }
>	: srcloc 'module' modid 'where' body
>		{ Module $1 $3 $5 }

> body :: { [AnyDecl Pr] }
>	: '{'  bodyaux '}'			{ $2 }
>	| open bodyaux close			{ $2 }

> bodyaux :: { [AnyDecl Pr] }
>	: optsemis topdecls	{ $2 }
>	| optsemis		  		{ [] }

> semis :: { () }
>	: optsemis ';'				{ () }

> optsemis :: { () }
>	: semis					{ () }
>	| {- empty -}				{ () }

-----------------------------------------------------------------------------
Top-Level Declarations

Note: The report allows topdecls to be empty. This would result in another
shift/reduce-conflict, so we don't handle this case here, but in bodyaux.

> topdecls :: { [AnyDecl Pr] }
>	: topdecls1 optsemis		{% checkRevDecls $1 }

> topdecls1 :: { [AnyDecl Pr] }
>	: topdecls1 semis topdecl	{ $3 : $1 }
>	| topdecl			{ [$1] }

> topdecl :: { AnyDecl Pr }
>	: srcloc 'type' conid typarams '=' type
>			{ AnyDecl $ TypeDecl $1 $3 $4 $6 }
>	| srcloc 'data' conid typarams '=' constrs
>			{ AnyDecl $ DataDecl $1 $3 (reverse $4) $6 }
> | decl		 { AnyDecl $1 }
> | goaldecl { AnyDecl $1 }

> decls :: { [Decl Fn Pr] }
>	: optsemis decls1 optsemis	{% checkRevFnDecls $2 }
>	| optsemis			{ [] }

> decls1 :: { [Decl Fn Pr] }
>	: decls1 semis decl		{ $3 : $1 }
>	| decl				{ [$1] }

> decl :: { Decl Fn Pr }
>	: signdecl			{ $1 }
>	| valdef			{ $1 }

> decllist :: { [Decl Fn Pr] }
>	: '{'  decls '}'		{ $2 }
>	| open decls close		{ $2 }

> signdecl :: { Decl Fn Pr }
>	: srcloc vars '::' polytype	{ TypeSig $1 (reverse $2) $4 }

> vars	:: { [VAR Pr] }
>	: vars ',' var			{ $3 : $1 }
>	| var				        { [$1] }

-----------------------------------------------------------------------------
Types

> type :: { Type Pr }
>	: dom '->' type		{ FunTy $1 $3 }
>	| btype				{ $1 }

> dom :: { Dom Pr }
> : btype 	{ Dom Nothing $1 Nothing }


> btype :: { Type Pr }
>	: btype atype			{ AppTy $1 $2 }
>	| atype				{ $1 }

> atype :: { Type Pr }
>	: gtycon						{ ConTy $1 }
>	| tyvar							{ VarTy $1 }
>	| '(' tupdoms ')'		{ TupleTy (length $2) (reverse $2) }
>	| '[' type ']'			{ listTy $2 }
>	| '(' type ')'			{ $2 }

> gtycon :: { TyCon Pr }
>	:  utycon			{ $1 }
>	| '(' ')'			{ unitTyCon }


> polytype :: { PolyType Pr }
> : type			{ ForallTy [] $1 }


> tupdoms	:: { [Dom Pr] }
>	: tupdoms ',' dom		{ $3 : $1 }
>	| dom  ',' dom		{ [$3, $1] }

> typaram :: { TyVAR Pr ::: Maybe Kind }
> : tyvar     { $1 ::: Nothing }

> typarams :: { TyParams Pr }
>	: typarams typaram	{ $2 : $1 }
>	| {- empty -}				{ [] }

-----------------------------------------------------------------------------
Datatype declarations

> constrs :: { [ConDecl Pr] }
>	: constrs '|' constr		{ $3 : $1 }
>	| constr			{ [$1] }

> constr :: { ConDecl Pr }
>	: srcloc scontype		{ ConDecl $1 (fst $2) (snd $2) }

> scontype :: { (TyNAME Pr, [Type Pr]) }
>	: btype				{% do { (c,ts) <- splitTyConApp $1;
>											  return (c,ts) } }

-----------------------------------------------------------------------------
Value definitions

> goaldecl :: { Decl Lg Pr }
> : srcloc goaltype varid '=' exp  { GoalDecl $1 $3 $2 NoPostTc $5 }

> goaltype :: { GoalType }
> : 'theorem' { TheoremGoal }
> | 'lemma'   { LemmaGoal }

> valdef :: { Decl Fn Pr }
> : srcloc varid apats rhs optwhere	{ FunBind Rec [Match $1 $2 $3 $4 $5] }
> | srcloc pat rhs optwhere 				{ PatBind $1 Rec $2 NoPostTc $3 $4 }

> optwhere :: { [Decl Fn Pr] }
>	: 'where' decllist		{ $2 }
>	| {- empty -}			{ [] }

> rhs	:: { Rhs Pr }
>	: '=' exp			{ UnGuardedRhs $2 }
>	| gdrhs				{ GuardedRhss  (reverse $1) NoOtherwise }

> gdrhs :: { [GuardedRhs Pr] }
>	: gdrhs gdrh			{ $2 : $1 }
>	| gdrh				{ [$1] }

> gdrh :: { GuardedRhs Pr }
>	: srcloc '|' exp0 '=' exp	{ GuardedRhs $1 $3 $5 }

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

> exp   :: { Exp Pr }
>	: exp0b ':' srcloc type  	{ Ann $3 $1 $4 }
>	| exp0				{ $1 }

> exp0 :: { Exp Pr }
>	: exp0a				{ $1 }
>	| exp0b				{ $1 }

> exp0a :: { Exp Pr }
>	: exp0b op exp10a		{ InfixApp $1 $2 $3 }
>	| exp10a			{ $1 }

> exp0b :: { Exp Pr }
>	: exp0b op exp10b		{ InfixApp $1 $2 $3 }
>	| exp10b			{ $1 }

> exp10a :: { Exp Pr }
>	: '\\' srcloc apats '->' exp	{ Lam $2 (reverse $3) $5 }
> | 'let' decllist 'in' exp	{ Let $2 $4 }
>	| 'if' exp 'then' exp 'else' exp { If $2 $4 $6 }
> | quantifier apats ',' exp  { QP $1 (reverse $2) $4 }

> quantifier :: { Quantifier }
> : 'exists'  { ExistsQ }
> | 'forall'  { ForallQ }

> exp10b :: { Exp Pr }
>	: 'case' exp 'of' altslist	{ Case $2 NoPostTc $4 }
>	| '-' fexp			{ PrefixApp (IntOp NegI) $2 }
>	| fexp				{ $1 }

> fexp :: { Exp Pr }
>	: fexp aexp			{ App $1 $2 }
> | aexp				{ $1 }

> apats :: { [Pat Pr] }
>	: apats apat			{ $2 : $1 }
> | apat				{ [$1] }


> pat   :: { Pat Pr }
>	: pat1 ':' type  	{ SigPat $1 $3 }
>	| pat1				{ $1 }

> pat1 :: { Pat Pr }
>	: fpat '::' pat1		{ InfixPat $1 ConsCon $3 }
>	| fpat			{ $1 }

> fpat :: { Pat Pr }
>	: con apats		{ ConPat $1 (reverse $2) }
> | apat				{ $1 }

> apat :: { Pat Pr }
>	: var '@' apat	{ AsPat $1 $3 }
> | apat1					{ $1 }

> apat1 :: { Pat Pr }
>	: var 			{ VarPat $1 }
> | con        { ConPat $1 [] }
> | literal			{ LitPat $1 }
>	| '(' pat ')'			{ ParenPat $2 }
>	| '(' tpats ')'			{ TuplePat (reverse $2) }
>	| '[' lpats ']'			{ ListPat (reverse $2) }
> | '_'							{ WildPat }

> tpats :: { [Pat Pr] }
>	: tpats ',' pat			{ $3 : $1 }
>	| pat ',' pat			{ [$3,$1] }

> lpats :: { [Pat Pr] }
>	: lpats ',' pat			{ $3 : $1 }
> | pat             { [$1] }
>	| {- empty -}			{ [] }

> aexp	:: { Exp Pr }
> : aexp1				{ $1 }

Note: The first two alternatives of aexp1 are not necessarily record
updates: they could be labeled constructions.

> aexp1	:: { Exp Pr }
> : aexp2				{ $1 }

According to the Report, the left section (e op) is legal iff (e op x)
parses equivalently to ((e) op x).  Thus e must be an exp0b.

> aexp2	:: { Exp Pr }
>	: var				{ Var $1 }
>	| gcon				{ $1 }
> | literal			{ Lit $1 }
>	| '(' exp ')'			{ Paren $2 }
>	| '(' texps ')'			{ Tuple (reverse $2) }
>	| '[' list ']'         { $2 }
>	| '(' exp0b op ')'		{ LeftSection $2 $3  }
>	| '(' op exp0 ')'		{ RightSection $2 $3 }

> commas :: { Int }
>	: commas ','			{ $1 + 1 }
>	| ','				{ 1 }

> texps :: { [Exp Pr] }
>	: texps ',' exp			{ $3 : $1 }
>	| exp ',' exp			{ [$3,$1] }

-----------------------------------------------------------------------------
List expressions

The rules below are little bit contorted to keep lexps left-recursive while
avoiding another shift/reduce-conflict.

> list :: { Exp Pr }
>	: exp				{ List [$1] }
>	| lexps 			{ List (reverse $1) }
>	| exp '..' exp	 		{ EnumFromTo $1 $3 }
>	| exp ',' exp '..' exp		{ EnumFromThenTo $1 $3 $5 }

> lexps :: { [Exp Pr] }
>	: lexps ',' exp 		{ $3 : $1 }
>	| exp ',' exp			{ [$3,$1] }

-----------------------------------------------------------------------------
Case alternatives

> altslist :: { [Alt Pr] }
>	: '{'  alts '}'			{ $2 }
>	| open alts close		{ $2 }

> alts :: { [Alt Pr] }
>	: optsemis alts1 optsemis	{ reverse $2 }

> alts1 :: { [Alt Pr] }
>	: alts1 semis alt		{ $3 : $1 }
>	| alt				{ [$1] }

> alt :: { Alt Pr }
>	: srcloc pat altrhs	{ Alt $1 $2 $3 }

> altrhs :: { Rhs Pr }
>	: '->' exp			{ UnGuardedRhs $2 }
>	| gdpats			{ GuardedRhss (reverse $1) NoOtherwise }

> gdpats :: { [GuardedRhs Pr] }
>	: gdpats gdpat			{ $2 : $1 }
>	| gdpat				{ [$1] }

> gdpat	:: { GuardedRhs Pr }
>	: srcloc '|' exp0 '->' exp	{ GuardedRhs $1 $3 $5 }

-----------------------------------------------------------------------------
Variables, Constructors and Operators.

> gcon :: { Exp Pr }
> : '(' ')'		{ Con (BuiltinCon UnitCon) }
>	| '[' ']'		{ Con (BuiltinCon NilCon) }
> | conid			{ Con (UserCon $1) }

> con :: { Con Pr }
> : '(' ')'		{ BuiltinCon UnitCon }
>	| '[' ']'		{ BuiltinCon NilCon }
> | conid			{ UserCon $1 }

> var 	:: { VAR Pr }
>	: varid			{ $1 }

> op	:: { Op }
>	: '::'			{ ConOp ConsCon }
> | '=='      { BoolOp EqB }


-----------------------------------------------------------------------------
Identifiers and Symbols

> varid :: { VAR Pr }
>	: VARID			{ mkOccName VarNS $1 }

> conid :: { VAR Pr }
>	: CONID			{ mkOccName ConNS $1 }

> tyvarid :: { VAR Pr }
>	: VARID			{ mkOccName TyVarNS $1 }

> tyconid :: { VAR Pr }
>	: CONID			{ mkOccName TyConNS $1 }

> literal :: { Lit }
>	: INT			{ IntLit $1 }

> srcloc :: { SrcLoc }	:	{% getSrcLoc }
 
-----------------------------------------------------------------------------
Layout

> open  :: { () }	:	{% pushCurrentContext }

> close :: { () }
>	: vccurly		{ () } -- context popped in lexer.
>	| error			{% popContext }

-----------------------------------------------------------------------------
Miscellaneous (mostly renamings)

> modid :: { ModuleName }
>	: CONID			{ ModName $1 }

> tyvar :: { TyVAR Pr }
>	: VARID			{ mkOccName TyVarNS $1 }

> utycon :: { TyCon Pr }
>	: tyconid			{ UserTyCon $1 }

-----------------------------------------------------------------------------

> {
> happyError :: P a
> happyError = fail "Parse error"

> -- | Parse of a string, which should contain a complete H! module.
> parseModule :: String -> ParseResult (Module Pr)
> parseModule = runParser parse

> -- | Parse of a string, which should contain a complete H! module.
> parseModuleWithMode :: ParseMode -> String -> ParseResult (Module Pr)
> parseModuleWithMode mode = runParserWithMode mode parse
> }
