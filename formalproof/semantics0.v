Require Export ZArith.
Require Export List.
Require Export Bool.

Require Export sflib.


Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.


Inductive ty: Type :=
| TyUnit: ty
| TyBool: ty
| TyChar: ty
| TyInt: ty
| TyPair: ty -> ty -> ty
| TyList: ty -> ty
| TyArrow: ty -> ty -> ty
.

Hint Constructors ty.

Inductive isComparable: ty -> Prop :=
| IsCompUnit: isComparable TyUnit
| IsCompBool: isComparable TyBool
| IsCompChar: isComparable TyChar
| IsCompInt: isComparable TyInt
| IsCompPair: forall Tfst Tsnd,
    isComparable Tfst ->
    isComparable Tsnd ->
    isComparable (TyPair Tfst Tsnd)
| IsCompList: forall Telem,
    isComparable Telem ->
    isComparable (TyList Telem)
.

Hint Constructors isComparable.


Inductive id: Type :=
| Id: nat -> id
.

Hint Constructors id.

Lemma eq_id_dec: forall (i1 i2: id), {i1 = i2} + {i1 <> i2}.
Proof.
  intros i1 i2.
  destruct i1 as [n1]. destruct i2 as [n2].
  destruct (eq_nat_dec n1 n2).
  auto.
  right. intros contra. inversion contra. auto.
Qed.

Lemma eq_id: forall T i (t0 t1: T),
    (if eq_id_dec i i then t0 else t1) = t0.
Proof.
  intros.
  destruct (eq_id_dec i i).
  - reflexivity.
  - exfalso. eauto.
Qed.

Lemma neq_id : forall T i0 i1 (t0 t1:T),
    i0 <> i1 ->
    (if eq_id_dec i0 i1 then t0 else t1) = t1.
Proof.
  intros.
  destruct (eq_id_dec i0 i1).
  - exfalso. eauto.
  - reflexivity.
Qed.

Inductive tm: Type :=
(* Error/Undefined *)
| TmError: tm

(* Unit *)
| TmUnit: tm

(* Bool *)
| TmTrue: tm
| TmFalse: tm
| TmNeg: tm -> tm
| TmAnd: tm -> tm -> tm
| TmOr: tm -> tm -> tm
| TmIf: tm -> tm -> tm -> tm

(* Char *)
| TmChar: nat -> tm

(* Integer *)
| TmInt: Z -> tm

(* Pair *)
| TmPair: tm -> tm -> tm
| TmFst: tm -> tm
| TmSnd: tm -> tm

(* List *)
| TmNil: tm
| TmCons: tm -> tm -> tm
| TmHead: tm -> tm
| TmTail: tm -> tm

(* Function *)
| TmLam: id -> ty -> tm -> tm
| TmApp: tm -> tm -> tm

(* Equality *)
| TmEq: tm -> tm -> tm

(* Variable *)
| TmVar: id -> tm

(* Local binding *)
| TmLet: id -> tm -> tm -> tm

(* Fixpoint binding *)
| TmFix: tm -> tm
.

Hint Constructors tm.



Inductive val: tm -> Prop :=
| ValError: val TmError

| ValUnit: val TmUnit

| ValTrue: val TmTrue
| ValFalse: val TmFalse

| ValChar: forall c,
    val (TmChar c)

| ValInt: forall z,
    val (TmInt z)

| ValPair: forall tfst tsnd,
    val (TmPair tfst tsnd)

| ValNil: val TmNil
| ValCons: forall thead ttail,
    val (TmCons thead ttail)

| ValLam: forall ipar Tpar tres,
    val (TmLam ipar Tpar tres)
.

Hint Constructors val.



Reserved Notation "'[' x0 '<-' t0 ']' t1" (at level 20).

Fixpoint subst (i: id) (s: tm) (t: tm): tm :=
  match t with
  | TmNeg tneg =>
    TmNeg ([i <- s] tneg)
  | TmAnd tleft tright =>
    TmAnd ([i <- s] tleft) ([i <- s] tright)
  | TmOr tleft tright =>
    TmOr ([i <- s] tleft) ([i <- s] tright)
  | TmIf tcond ttrue tfalse =>
    TmIf ([i <- s] tcond) ([i <- s] ttrue) ([i <- s] tfalse)

  | TmPair tfst tsnd =>
    TmPair ([i <- s] tfst) ([i <- s] tsnd)
  | TmFst tpair =>
    TmFst ([i <- s] tpair)
  | TmSnd tpair =>
    TmSnd ([i <- s] tpair)

  | TmCons thead ttail =>
    TmCons ([i <- s] thead) ([i <- s] ttail)
  | TmHead tlist =>
    TmHead ([i <- s] tlist)
  | TmTail tlist =>
    TmTail ([i <- s] tlist)

  | TmLam ipar Tpar tres =>
    TmLam ipar Tpar (if eq_id_dec i ipar then tres else [i <- s] tres)
  | TmApp tlam tapp =>
    TmApp ([i <- s] tlam) ([i <- s] tapp)

  | TmEq tleft tright =>
    TmEq ([i <- s] tleft) ([i <- s] tright)

  | TmVar ivar =>
    if eq_id_dec i ivar then s else t

  | TmLet ilet tlet tin =>
    TmLet ilet
          ([i <- s] tlet)
          (if eq_id_dec i ilet then tin else [i <- s] tin)

  | TmFix tfix =>
    TmFix ([i <- s] tfix)

  | _ => t
  end

where "'[' x '<-' t0 ']' t1" := (subst x t0 t1)
.



Definition Relation (X: Type): Type := X -> X -> Prop.

Reserved Notation " t0 '==>' t1 " (at level 40).

Inductive smst: Relation tm :=
| SmstNegStep: forall tneg0 tneg1,
    tneg0 ==> tneg1 ->
    TmNeg tneg0 ==> TmNeg tneg1
| SmstNegTrue:
    TmNeg TmTrue ==> TmFalse
| SmstNegFalse:
    TmNeg TmFalse ==> TmTrue
| SmstNegError:
    TmNeg TmError ==> TmError
| SmstAndLeftStep: forall tleft0 tleft1 tright,
    tleft0 ==> tleft1 ->
    TmAnd tleft0 tright ==> TmAnd tleft1 tright
| SmstAndLeftFalse: forall tright,
    TmAnd TmFalse tright ==> TmFalse
| SmstAndLeftError: forall tright,
    TmAnd TmError tright ==> TmError
| SmstAndRightStep: forall tright0 tright1,
    tright0 ==> tright1 ->
    TmAnd TmTrue tright0 ==> TmAnd TmTrue tright1
| SmstAndRightFalse:
    TmAnd TmTrue TmFalse ==> TmFalse
| SmstAndRightError:
    TmAnd TmTrue TmError ==> TmError
| SmstAndTrue:
    TmAnd TmTrue TmTrue ==> TmTrue
| SmstOrLeftStep: forall tleft0 tleft1 tright,
    tleft0 ==> tleft1 ->
    TmOr tleft0 tright ==> TmOr tleft1 tright
| SmstOrLeftTrue: forall tright,
    TmOr TmTrue tright ==> TmTrue
| SmstOrLeftError: forall tright,
    TmOr TmError tright ==> TmError
| SmstOrRightStep: forall tright0 tright1,
    tright0 ==> tright1 ->
    TmOr TmFalse tright0 ==> TmOr TmFalse tright1
| SmstOrRightTrue:
    TmOr TmFalse TmTrue ==> TmTrue
| SmstOrRightError:
    TmOr TmFalse TmError ==> TmError
| SmstOrFalse:
    TmOr TmFalse TmFalse ==> TmFalse
| SmstIfStep: forall tcond0 tcond1 ttrue tfalse,
    tcond0 ==> tcond1 ->
    TmIf tcond0 ttrue tfalse ==> TmIf tcond1 ttrue tfalse
| SmstIfTrue: forall ttrue tfalse,
    TmIf TmTrue ttrue tfalse ==> ttrue
| SmstIfFalse: forall ttrue tfalse,
    TmIf TmFalse ttrue tfalse ==> tfalse
| SmstIfError: forall ttrue tfalse,
    TmIf TmError ttrue tfalse ==> TmError

| SmstFstStep: forall tpair0 tpair1,
    tpair0 ==> tpair1 ->
    TmFst tpair0 ==> TmFst tpair1
| SmstFstPair: forall tfst tsnd,
    TmFst (TmPair tfst tsnd) ==> tfst
| SmstFstError:
    TmFst TmError ==> TmError
| SmstSndStep: forall tpair0 tpair1,
    tpair0 ==> tpair1 ->
    TmSnd tpair0 ==> TmSnd tpair1
| SmstSndPair: forall tfst tsnd,
    TmSnd (TmPair tfst tsnd) ==> tsnd
| SmstSndError:
    TmSnd TmError ==> TmError

| SmstHeadStep: forall tlist0 tlist1,
    tlist0 ==> tlist1 ->
    TmHead tlist0 ==> TmHead tlist1
| SmstHeadNil:
    TmHead TmNil ==> TmError
| SmstHeadCons: forall thead ttail,
    TmHead (TmCons thead ttail) ==> thead
| SmstHeadError:
    TmHead TmError ==> TmError
| SmstTailStep: forall tlist0 tlist1,
    tlist0 ==> tlist1 ->
    TmTail tlist0 ==> TmTail tlist1
| SmstTailNil:
    TmTail TmNil ==> TmError
| SmstTailCons: forall thead ttail,
    TmTail (TmCons thead ttail) ==> ttail
| SmstTailError:
    TmTail TmError ==> TmError

| SmstAppStep: forall tlam0 tlam1 tapp,
    tlam0 ==> tlam1 ->
    TmApp tlam0 tapp ==> TmApp tlam1 tapp
| SmstAppLam: forall ipar Tpar tres tapp,
    TmApp (TmLam ipar Tpar tres) tapp ==> [ipar <- tapp] tres
| SmstAppError: forall tapp,
    TmApp TmError tapp ==> TmError

| SmstEqLeftStep: forall tleft0 tleft1 tright,
    tleft0 ==> tleft1 ->
    TmEq tleft0 tright ==> TmEq tleft1 tright
| SmstEqLeftError: forall tright,
    TmEq TmError tright ==> TmError
| SmstEqRightStep: forall vleft tright0 tright1,
    val vleft ->
    vleft <> TmError ->
    tright0 ==> tright1 ->
    TmEq vleft tright0 ==> TmEq vleft tright1
| SmstEqRightError: forall vleft,
    val vleft ->
    vleft <> TmError ->
    TmEq vleft TmError ==> TmError
| SmstEqUnitTrue:
    TmEq TmUnit TmUnit ==> TmTrue
| SmstEqBoolTrue0:
    TmEq TmTrue TmTrue ==> TmTrue
| SmstEqBoolTrue1:
    TmEq TmFalse TmFalse ==> TmTrue
| SmstEqBoolFalse0:
    TmEq TmTrue TmFalse ==> TmFalse
| SmstEqBoolFalse1:
    TmEq TmFalse TmTrue ==> TmFalse
| SmstEqCharTrue: forall c0 c1,
    c0 = c1 ->
    TmEq (TmChar c0) (TmChar c1) ==> TmTrue
| SmstEqCharFalse: forall c0 c1,
    c0 <> c1 ->
    TmEq (TmChar c0) (TmChar c1) ==> TmFalse
| SmstEqIntTrue: forall z0 z1,
    z0 = z1 ->
    TmEq (TmInt z0) (TmInt z1) ==> TmTrue
| SmstEqIntFalse: forall z0 z1,
    z0 <> z1 ->
    TmEq (TmInt z0) (TmInt z1) ==> TmFalse
| SmstEqPair: forall tfst0 tsnd0 tfst1 tsnd1,
    TmEq (TmPair tfst0 tsnd0) (TmPair tfst1 tsnd1) ==>
    TmAnd (TmEq tfst0 tfst1) (TmEq tsnd0 tsnd1)
| SmstEqListNilTrue:
    TmEq TmNil TmNil ==> TmTrue
| SmstEqListFalse0: forall thead1 ttail1,
    TmEq TmNil (TmCons thead1 ttail1) ==> TmFalse
| SmstEqListFalse1: forall thead0 ttail0,
    TmEq (TmCons thead0 ttail0) TmNil ==> TmFalse
| SmstEqListCons: forall thead0 ttail0 thead1 ttail1,
    TmEq (TmCons thead0 ttail0) (TmCons thead1 ttail1) ==>
    TmAnd (TmEq thead0 thead1) (TmEq ttail0 ttail1)

| SmstLet: forall ilet tlet tin,
    TmLet ilet tlet tin ==> [ilet <- tlet] tin

| SmstFixStep: forall tfix0 tfix1,
    tfix0 ==> tfix1 ->
    TmFix tfix0 ==> TmFix tfix1
| SmstFixLam: forall ilam Tlam tlam,
    TmFix (TmLam ilam Tlam tlam) ==> [ilam <- TmFix (TmLam ilam Tlam tlam)] tlam
| SmstFixError:
    TmFix TmError ==> TmError

where "t0 '==>' t1" := (smst t0 t1)
.

Hint Constructors smst.



Inductive mlt {T: Type} (R: Relation T) : Relation T :=
  | mltRefl  : forall (t: T), mlt R t t
  | mltStep : forall (t0 t1 t2 : T),
                    R t0 t1 ->
                    mlt R t1 t2 ->
                    mlt R t0 t2.

Hint Constructors mlt.

Theorem mltLift: forall (T: Type) (R: Relation T) (t0 t1: T),
    R t0 t1 ->
    mlt R t0 t1.
Proof.
  intros T R t0 t1 smst.
  eauto.
Qed.

Theorem mltTrans: forall (T: Type) (R: Relation T) (t0 t1 t2: T),
    mlt R t0 t1 ->
    mlt R t1 t2 ->
    mlt R t0 t2.
Proof.
  intros T R t0 t1 t2 mlt0 mlt1.
  induction mlt0 as [t0|t0 t1].
  - auto.
  - eauto.
Qed.



Definition idPartialMap (K: Type): Type := id -> option K.

Definition emptyMap {K: Type}: idPartialMap K := fun _ => None.
Definition extend {K: Type} (G: idPartialMap K) (i0: id) (T0: K):
  idPartialMap K :=
  fun i1 => if eq_id_dec i0 i1 then Some T0 else G i1.

Hint Unfold emptyMap.
Hint Unfold extend.

Lemma extend_eq: forall K (G: idPartialMap K) i T,
    (extend G i T) i = Some T.
Proof.
  intros.
  unfold extend. rewrite eq_id. reflexivity.
Qed.

Lemma extend_neq: forall K (G: idPartialMap K) i0 i1 T,
    i0 <> i1 ->
    (extend G i0 T) i1 = G i1.
Proof.
  intros.
  unfold extend. rewrite neq_id; auto.
Qed.

Definition tyCtxt: Type := idPartialMap ty.

Reserved Notation "TC '|-' t ':|' T" (at level 40).

Inductive hasTy: tyCtxt -> tm -> ty -> Prop :=
| HasTyError: forall TC T,
    TC |- TmError :| T

| HasTyUnit: forall TC,
    TC |- TmUnit :| TyUnit

| HasTyTrue: forall TC,
    TC |- TmTrue :| TyBool
| HasTyFalse: forall TC,
    TC |- TmFalse :| TyBool
| HasTyNeg: forall TC tneg,
    TC |- tneg :| TyBool ->
    TC |- TmNeg tneg :| TyBool
| HasTyAnd: forall TC tleft tright,
    TC |- tleft :| TyBool ->
    TC |- tright :| TyBool ->
    TC |- TmAnd tleft tright :| TyBool
| HasTyOr: forall TC tleft tright,
    TC |- tleft :| TyBool ->
    TC |- tright :| TyBool ->
    TC |- TmOr tleft tright :| TyBool
| HasTyIf: forall TC tcond ttrue tfalse Tif,
    TC |- tcond :| TyBool ->
    TC |- ttrue :| Tif ->
    TC |- tfalse :| Tif ->
    TC |- TmIf tcond ttrue tfalse :| Tif

| HasTyChar: forall TC c,
    TC |- TmChar c :| TyChar

| HasTyInt: forall TC z,
    TC |- TmInt z :| TyInt

| HasTyPair: forall TC tfst Tfst tsnd Tsnd,
    TC |- tfst :| Tfst ->
    TC |- tsnd :| Tsnd ->
    TC |- TmPair tfst tsnd :| TyPair Tfst Tsnd
| HasTyFst: forall TC tpair Tfst Tsnd,
    TC |- tpair :| TyPair Tfst Tsnd ->
    TC |- TmFst tpair :| Tfst
| HasTySnd: forall TC tpair Tfst Tsnd,
    TC |- tpair :| TyPair Tfst Tsnd ->
    TC |- TmSnd tpair :| Tsnd

| HasTyNil: forall TC Telem,
    TC |- TmNil :| TyList Telem
| HasTyCons: forall TC thead ttail Telem,
    TC |- thead :| Telem ->
    TC |- ttail :| TyList Telem ->
    TC |- TmCons thead ttail :| TyList Telem
| HasTyHead: forall TC tlist Telem,
    TC |- tlist :| TyList Telem ->
    TC |- TmHead tlist :| Telem
| HasTyTail: forall TC tlist Telem,
    TC |- tlist :| TyList Telem ->
    TC |- TmTail tlist :| TyList Telem

| HasTyLam: forall TC ipar Tpar tres Tres,
    (extend TC ipar Tpar) |- tres :| Tres ->
    TC |- TmLam ipar Tpar tres :| TyArrow Tpar Tres
| HasTyApp: forall TC tlam Tres tapp Tapp,
    TC |- tlam :| TyArrow Tapp Tres ->
    TC |- tapp :| Tapp ->
    TC |- TmApp tlam tapp :| Tres

| HasTyEq: forall TC tleft tright Teq,
    TC |- tleft :| Teq ->
    TC |- tright :| Teq ->
    isComparable Teq ->
    TC |- TmEq tleft tright :| TyBool

| HasTyVar: forall TC i Tvar,
    TC i = Some Tvar ->
    TC |- TmVar i :| Tvar

| HasTyLet: forall TC ilet tlet Tlet tin Tin,
    TC |- tlet :| Tlet ->
    (extend TC ilet Tlet) |- tin :| Tin ->
    TC |- TmLet ilet tlet tin :| Tin
| HasTyFix: forall TC tfix Tfix ,
    TC |- tfix :| TyArrow Tfix Tfix ->
    TC |- TmFix tfix :| Tfix

where "TC '|-' t ':|' T" := (hasTy TC t T)
.

Hint Constructors hasTy.


(* Fixpoint complexness (t: tm): nat := *)
(*   match t with *)
(*   | TmError => 0 *)

(*   | TmUnit => 0 *)

(*   | TmTrue => 0 *)
(*   | TmFalse => 0 *)

(*   | TmChar => 0 *)

(*   | TmInt => 0 *)

(*   | TmPair tfst tsnd => *)
(*     max (complexness tfst) (complexness tsnd) + 1 *)
(*   | TmFst (TmPair tfst tsnd) => *)
(*     complexness tfst *)
(*   | TmFst _ => 0 *)
(*   | TmSnd (TmPair tfst tsnd) => *)
(*     complexness tsnd *)
(*   | TmSnd _ => 0 *)

(*   | TmNil => 0 *)
(*   | TmCons thead ttail => *)
(*     complexness thead + complexness ttail *)
(*   | TmHead (TmCons thead ttail) => *)
(*     complexness thead *)
(*   | TmHead _ => 0 *)
(*   | TmTail (TmCons thead ttail) => *)
(*     complexness ttail *)
(*   | TmTail _ => 0 *)

(*   | TmLam ipar Tpar tres => *)
(*     complexness tres + 1 *)
(*   | TmApp tlam tapp => *)
(*     complexness tlam * complexness tapp *)

(*   | TmVar ivar => 0 *)

(*   | TmEq tleft tright => *)
(*     max (complexness tleft) (complexness tright) + 1 *)
(*   | TmIf *)

(*   | TmLet: id -> tm -> tm -> tm *)
(*   | TmFix: tm -> tm *)



Theorem progress : forall t T,
    emptyMap |- t :| T ->
    val t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T typed.
  remember emptyMap as G.
  generalize dependent HeqG.
  induction typed; intros;
    subst; eauto;
      try (right;
           destruct IHtyped; subst; eauto;
           [inversion typed; subst; try solve by inversion; eauto |
            inversion H; eauto])...

  - (* TmAnd *)
    right.
    destruct IHtyped1; subst...
    + inversion typed1; subst; inversion H...
      destruct IHtyped2; subst...
      * inversion typed2; subst; inversion H0...
      * inversion typed2; subst; inversion H0; eauto;
          inversion H0; exists (TmAnd TmTrue x); constructor; eauto;
            intros contra; inversion contra.
    + inversion H...
  - (* TmOr *)
    right.
    destruct IHtyped1; subst...
    + inversion typed1; subst; inversion H...
      * destruct IHtyped2; subst...
        { inversion typed2; subst; inversion H0... }
        { inversion H0... }
    + inversion H...
  - (* TmIf *)
    right.
    destruct IHtyped1; subst...
    + inversion typed1; subst; inversion H...
    + inversion H...

  - (* TmApp *)
    right.
    destruct IHtyped1; subst...
    + inversion typed1; subst; inversion H...
    + inversion H...

  - (* TmEq *)
    right.
    destruct IHtyped1; subst...
    + destruct IHtyped2; subst...
      * inversion typed1; subst; inversion H0; eauto;
          inversion typed2; subst; inversion H1;
            try (exists TmError; constructor; eauto;
                    intros contra; by inversion contra);
            try (exists TmTrue; constructor; by eauto);
            try (exists TmFalse; constructor; by eauto)...
        { destruct (eq_nat_dec c c0).
          - exists TmTrue; constructor; subst...
          - exists TmFalse; constructor;
              intros contra; inversion contra; subst... }
        { destruct (Z.eq_dec z z0).
          - exists TmTrue; constructor; subst...
          - exists TmFalse; constructor;
              intros contra; inversion contra; subst... }
        { inversion H. }
      * remember tleft as tl.
        inversion typed1; subst; inversion H0; eauto;
          inversion H1; exists (TmEq tleft x); subst; constructor; eauto;
            intros contra; by inversion contra.
    + inversion H0...

  - (* TmVar *)
    inversion H.
Qed.

Hint Immediate progress.


Inductive freeVar: id -> tm -> Prop :=
| FreeVarNeg: forall i tneg,
    freeVar i tneg ->
    freeVar i (TmNeg tneg)
| FreeVarAndLeft: forall i tleft tright,
    freeVar i tleft ->
    freeVar i (TmAnd tleft tright)
| FreeVarAndRight: forall i tleft tright,
    freeVar i tright ->
    freeVar i (TmAnd tleft tright)
| FreeVarOrLeft: forall i tleft tright,
    freeVar i tleft ->
    freeVar i (TmOr tleft tright)
| FreeVarOrRight: forall i tleft tright,
    freeVar i tright ->
    freeVar i (TmOr tleft tright)
| FreeVarIfCond: forall i tcond ttrue tfalse,
    freeVar i tcond ->
    freeVar i (TmIf tcond ttrue tfalse)
| FreeVarIfTrue: forall i tcond ttrue tfalse,
    freeVar i ttrue ->
    freeVar i (TmIf tcond ttrue tfalse)
| FreeVarIfFalse: forall i tcond ttrue tfalse,
    freeVar i tfalse ->
    freeVar i (TmIf tcond ttrue tfalse)

| FreeVarPairFst: forall i tfst tsnd,
    freeVar i tfst ->
    freeVar i (TmPair tfst tsnd)
| FreeVarPairSnd: forall i tfst tsnd,
    freeVar i tsnd ->
    freeVar i (TmPair tfst tsnd)
| FreeVarFst: forall i tpair,
    freeVar i tpair ->
    freeVar i (TmFst tpair)
| FreeVarSnd: forall i tpair,
    freeVar i tpair ->
    freeVar i (TmSnd tpair)

| FreeVarConsHead: forall i thead ttail,
    freeVar i thead ->
    freeVar i (TmCons thead ttail)
| FreeVarConsTail: forall i thead ttail,
    freeVar i ttail ->
    freeVar i (TmCons thead ttail)
| FreeVarHead: forall i tlist,
    freeVar i tlist ->
    freeVar i (TmHead tlist)
| FreeVarTail: forall i tlist,
    freeVar i tlist ->
    freeVar i (TmTail tlist)

| FreeVarLam: forall i ipar Tpar tres,
    i <> ipar ->
    freeVar i tres ->
    freeVar i (TmLam ipar Tpar tres)
| FreeVarAppLam: forall i tlam tapp,
    freeVar i tlam ->
    freeVar i (TmApp tlam tapp)
| FreeVarAppApp: forall i tlam tapp,
    freeVar i tapp ->
    freeVar i (TmApp tlam tapp)

| FreeVarEqLeft: forall i tleft tright,
    freeVar i tleft ->
    freeVar i (TmEq tleft tright)
| FreeVarEqRight: forall i tleft tright,
    freeVar i tright ->
    freeVar i (TmEq tleft tright)

| FreeVarVar: forall i,
    freeVar i (TmVar i)

| FreeVarLetLet: forall i ilet tlet tin,
    freeVar i tlet ->
    freeVar i (TmLet ilet tlet tin)
| FreeVarLetIn: forall i ilet tlet tin,
    i <> ilet ->
    freeVar i tin ->
    freeVar i (TmLet ilet tlet tin)

| FreeVarFix: forall i tfix,
    freeVar i tfix ->
    freeVar i (TmFix tfix)
.

Hint Constructors freeVar.


Lemma context_invariance: forall (TC0 TC1: tyCtxt) t T,
    TC0 |- t :| T ->
    (forall i, freeVar i t -> TC0 i = TC1 i) ->
    TC1 |- t :| T.
Proof with eauto.
  intros TC0 TC1 t T typed eqFreeVar.
  generalize dependent TC1.
  induction typed; intros;
    try (constructor; by eauto)...
  - (* TmLam *)
    constructor.
    apply IHtyped. intros.
    unfold extend.
    destruct (eq_id_dec ipar i)...
  - (* TmApp *)
    econstructor...
  - (* TmBool *)
    econstructor...
  - (* TmVar *)
    constructor. rewrite <- eqFreeVar...
  - (* TmLet *)
    econstructor.
    + apply IHtyped1. intros.
      apply eqFreeVar...
    + apply IHtyped2. intros.
      unfold extend.
      destruct (eq_id_dec ilet i)...
Qed.

Hint Immediate context_invariance.


Lemma free_in_context: forall TC i t T0,
    TC |- t :| T0 ->
    freeVar i t ->
    exists T1, TC i = Some T1.
Proof with eauto.
  intros TC i t T0 typed free.
  induction typed; intros; inversion free; subst...
  - (* TmLam *)
    destruct IHtyped... exists x.
    rewrite <- H. unfold extend.
    rewrite neq_id...
  - (* TmLet *)
    destruct IHtyped2... exists x.
    rewrite <- H. unfold extend.
    rewrite neq_id...
Qed.

Hint Immediate free_in_context.


Lemma substitution_preserves_typing: forall TC i s S t T,
    (extend TC i S) |- t :| T ->
    emptyMap |- s :| S ->
    TC |- ([i <- s] t) :| T.
Proof with eauto.
  intros TC i s S t T typed0 typed1.
  generalize dependent T.
  generalize dependent S.
  generalize dependent s.
  generalize dependent i.
  generalize dependent TC.
  induction t; intros; inversion typed0;
    try (constructor; by eauto);
    try (simpl; econstructor; by eauto); subst; simpl...
  - (* TmLam *)
    constructor.
    destruct (eq_id_dec i0 i).
    + eapply context_invariance...
      intros. subst. unfold extend.
      destruct (eq_id_dec i i1)...
    + eapply IHt...
      eapply context_invariance...
      intros. subst. unfold extend.
      destruct (eq_id_dec i i1)...
      subst. rewrite neq_id...
  - (* TmVar *)
    destruct (eq_id_dec i0 i).
    + subst. rewrite extend_eq in H1.
      inversion H1; subst. clear H1.
      eapply context_invariance... intros.
      destruct (free_in_context _ _ _ T typed1 H).
      inversion H0.
    + econstructor.
      rewrite <- H1. unfold extend.
      rewrite neq_id...
  - (* TmLet *)
    destruct (eq_id_dec i0 i).
    + econstructor...
      eapply context_invariance...
      intros. subst. unfold extend.
      destruct (eq_id_dec i i1)...
    + econstructor...
      eapply IHt2...
      eapply context_invariance...
      intros. subst. unfold extend.
      destruct (eq_id_dec i i1); destruct (eq_id_dec i0 i1); subst...
      exfalso...
Qed.

Hint Immediate substitution_preserves_typing.


Theorem preservation: forall t0 t1 T,
    emptyMap |- t0 :| T ->
    t0 ==> t1 ->
    emptyMap |- t1 :| T.
Proof with eauto.
  intros t0 t1 T typed step.
  remember emptyMap as TC. generalize dependent HeqTC.
  generalize dependent t1.
  induction typed; intros; subst;
    try (inversion step; subst;
         inversion typed; by eauto);
    try (inversion step; subst; by eauto)...
  - (* TmApp *)
    inversion step; subst...
    eapply substitution_preserves_typing...
    inversion typed1...
  - (* TmEq *)
    inversion step; subst; try (econstructor; by eauto)...
    + inversion typed1; subst;
        inversion typed2; subst;
          inversion H; subst.
      econstructor; econstructor...
    + inversion typed1; subst;
        inversion typed2; subst;
          inversion H; subst.
      econstructor; econstructor...
  - (* TmFix *)
    inversion step; subst...
    eapply substitution_preserves_typing...
    inversion typed; subst...
Qed.

Hint Immediate preservation.



Definition nmlfm {T: Type} (R: Relation T) (t0: T): Prop :=
  ~ exists t1, R t0 t1.

Hint Unfold nmlfm.

Notation stnmlfm := (nmlfm smst).

Notation mltst := (mlt smst).
Notation "t0 '==>*' t1" := (mltst t0 t1) (at level 40).

Theorem soundness: forall t0 t1 T,
    emptyMap |- t0 :| T ->
    t0 ==>* t1 ->
    ~ stnmlfm t1 \/ val t1.
Proof with eauto.
  intros t0 t1 T typed mltstep.
  induction mltstep...
  - apply progress in typed.
    destruct typed...
Qed.

Hint Immediate soundness.
