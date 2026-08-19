(**
 * Copyright (C) 2025 SkyLabs AI, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BlueRock Exception for use over network, see repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.cpp.stdlib.atomic.inc_int_cpp.

Require Import skylabs.cpp.spec.concepts.
Require Export skylabs.cpp.stdlib.atomic.pred.

Module atomic_specs (Import atomic : ATOMIC_PREDS).

  #[global] Hint Opaque R : sl_opacity.

  Section spec.
    Context `{Σ : cpp_logic} {σ : genv}.
    Context (ty : type).
    Context `{!PrimVal ty A,!DefaultValue ty A}.
    Abbreviation s := (class_name ty) (only parsing).	(** [Atomic<T>] *)
    Abbreviation b0 := (base_name ty) (only parsing).
    Abbreviation b1 := (base_name1 ty) (only parsing).
    Abbreviation R := (R ty).
    Abbreviation bR q v := (_derived b0 b1 ,, _derived b1 s |-> R q%cQp v) (only parsing).

    Definition default_ctor : mpred :=
      specify.template.ctor s [] $
        \this this
        \post this |-> R 1$m (default_val ty).
    #[global] Hint Opaque default_ctor : sl_opacity.
    #[global] Arguments default_ctor : simpl never.
    Definition SpecFor_default_ctor := RegisterSpec default_ctor.
    #[global] Existing Instance SpecFor_default_ctor.

    Definition ctor : mpred :=
      specify.template.ctor s [ty] $
        \this this
        \arg{n} "v" (Vinj ty n)
        \post this |-> R 1$m n.
    #[global] Hint Opaque ctor : sl_opacity.
    #[global] Arguments ctor : simpl never.
    Definition SpecFor_ctor := RegisterSpec ctor.
    #[global] Existing Instance SpecFor_ctor.

    Definition dtor : mpred :=
      specify.template.dtor s $
        \this this
        \pre{n} this |-> R 1$m n
        \post emp.
    #[global] Hint Opaque dtor : sl_opacity.
    #[global] Arguments dtor : simpl never.
    Definition SpecFor_dtor := RegisterSpec dtor.
    #[global] Existing Instance SpecFor_dtor.

    (** *** <<load>> & <<store>> *)
    Definition do_load (this : ptr) (K : A -> mpred) : mpred :=
      AR1 << ∃∃ n q, this |-> bR q n >> @ top, empty << K n >>.
    #[global] Hint Opaque do_load : typeclass_instances sl_opacity.

    Definition load : mpred :=
      specify.template.method b0 "load" function_qualifiers.N ty [Tmemory_order] $
        \this this
        \arg "mo" (memory_order.to_val memory_order.seq_cst)
        \pre{K} do_load this K
        \post{n}[Vinj ty n] K n.
    #[global] Hint Opaque load : sl_opacity.
    #[global] Arguments load : simpl never.
    Definition SpecFor_load := RegisterSpec load.
    #[global] Existing Instance SpecFor_load.

    Definition load_const : mpred :=
      specify.template.method b0 "load" function_qualifiers.Nc ty [Tmemory_order] $
        \this this
        \arg "mo" (memory_order.to_val memory_order.seq_cst)
        \pre{K} do_load this K
        \post{n}[Vinj ty n] K n.
    #[global] Hint Opaque load_const : sl_opacity.
    #[global] Arguments load_const : simpl never.
    Definition SpecFor_load_const := RegisterSpec load_const.
    #[global] Existing Instance SpecFor_load_const.

    Definition do_store (this : ptr) (n : A) (K : mpred) : mpred :=
      AC1 << ∀ m, this |-> bR 1$m m >> @ top, empty
          << this |-> bR 1$m n, COMM K >>.
    #[global] Hint Opaque do_store : typeclass_instances sl_opacity.

    Definition store : mpred :=
      specify.template.method b0 "store" function_qualifiers.N Tvoid [ty; Tmemory_order] $
        \this this
        \arg{n} "v" (Vinj ty n)
        \arg "mo" (memory_order.to_val memory_order.seq_cst)
        \pre{K} do_store this n K
        \post K.
    #[global] Hint Opaque store : sl_opacity.
    #[global] Arguments store : simpl never.
    Definition SpecFor_store := RegisterSpec store.
    #[global] Existing Instance SpecFor_store.

    (** *** <<operator=>> *)
    Definition assign : mpred :=
      specify.template.op b0 OOEqual function_qualifiers.N ty [ty] $
        \this this
        \arg{n} "v" (Vinj ty n)
        \pre{K} do_store this n K
        \post[Vinj ty n] K.
    #[global] Hint Opaque assign : sl_opacity.
    #[global] Arguments assign : simpl never.
    Definition SpecFor_assign := RegisterSpec assign.
    #[global] Existing Instance SpecFor_assign.

    (** *** <<operator ty>> *)
    Definition cast : mpred :=
      specify.template.conv b0 ty function_qualifiers.Nc $
        \this this
        \pre{K} do_load this K
        \post{n}[Vinj ty n] K n.
    #[global] Hint Opaque cast : sl_opacity.
    #[global] Arguments cast : simpl never.
    Definition SpecFor_cast := RegisterSpec cast.
    #[global] Existing Instance SpecFor_cast.

    (** *** <<exchange>> *)
    Definition do_exchange (this : ptr) (n : A) (K : A -> mpred) : mpred :=
      AU1 << ∀ m, this |-> bR 1$m m >> @ top, empty
          <<      this |-> bR 1$m n, COMM K m >>.
    #[global] Hint Opaque do_exchange : typeclass_instances sl_opacity.

    Definition exchange : mpred :=
      specify.template.method b0 "exchange" function_qualifiers.N ty
          [ty; Tmemory_order] $
        \this this
        \arg{desired} "desired" (Vinj ty desired)
        \arg "mo" (memory_order.to_val memory_order.seq_cst)
        \pre{K} do_exchange this desired K
        \post{m}[Vinj ty m] K m.
    #[global] Hint Opaque exchange : sl_opacity.
    #[global] Arguments exchange : simpl never.
    Definition SpecFor_exchange := RegisterSpec exchange.
    #[global] Existing Instance SpecFor_exchange.

    (** *** <<compare_exchange_weak>> & <<compare_exchange_strong>> *)
    Definition do_compare_exchange (weak : bool) (this expected_p : ptr) (expected desired : A)
        (K : bool -> mpred) : mpred :=
      AU1 << ∀ cur, this |-> bR 1$m cur >> @ top, empty
        << ∃ success m',
          [| if weak then (* lifting the test on [weak] is probably a bit easier to work with *)
               (success = true /\ cur = expected /\ m' = desired) \/
               (success = false /\ m' = cur)
             else
               (success = true /\ cur = expected /\ m' = desired) \/
               (success = false /\ cur <> expected /\ m' = cur)
          |] **
          this |-> bR 1$m m',
        COMM
          expected_p |-> primR ty 1$m (Vinj ty cur) -*
          K success
        >>.
    #[global] Hint Opaque do_compare_exchange : typeclass_instances sl_opacity.

    (** NOTE: the difference between the following two specs is not immediately obvious. *)
    Definition compare_exchange_strong : mpred :=
      specify.template.method b0 "compare_exchange_strong" function_qualifiers.N "bool"
          [Tref ty; ty; Tmemory_order; Tmemory_order] $
        \this this
        \arg{expected_p} "o" (Vref expected_p)
        \arg{desired} "n" (Vinj ty desired)
        \arg "mo_success" (memory_order.to_val memory_order.seq_cst)
        \arg "mo_failure" (memory_order.to_val memory_order.seq_cst)
        \pre{expected} expected_p |-> primR ty 1$m (Vinj ty expected)
        \pre{K} do_compare_exchange false this expected_p expected desired K
        \post{b}[Vbool b] K b.
    #[global] Hint Opaque compare_exchange_strong : sl_opacity.
    #[global] Arguments compare_exchange_strong : simpl never.
    Definition SpecFor_compare_exchange_strong := RegisterSpec compare_exchange_strong.
    #[global] Existing Instance SpecFor_compare_exchange_strong.

    Definition compare_exchange_strong_1 : mpred :=
      specify.template.method b0 "compare_exchange_strong" function_qualifiers.N "bool"
        [Tref ty; ty; Tmemory_order] $
        \this this
        \arg{expected_p} "o" (Vref expected_p)
        \arg{desired} "n" (Vinj ty desired)
        \arg "mo" (memory_order.to_val memory_order.seq_cst)
        \pre{expected} expected_p |-> primR ty 1$m (Vinj ty expected)
        \pre{K} do_compare_exchange false this expected_p expected desired K
        \post{b}[Vbool b] K b.
    #[global] Hint Opaque compare_exchange_strong_1 : sl_opacity.
    #[global] Arguments compare_exchange_strong_1 : simpl never.
    Definition SpecFor_compare_exchange_strong_1 := RegisterSpec compare_exchange_strong_1.
    #[global] Existing Instance SpecFor_compare_exchange_strong_1.

    Definition compare_exchange_weak : mpred :=
      specify.template.method b0 "compare_exchange_weak" function_qualifiers.N "bool"
        [Tref ty; ty; Tmemory_order; Tmemory_order] $
        \this this
        \arg{expected_p} "o" (Vref expected_p)
        \arg{desired} "n" (Vinj ty desired)
        \arg "mo_success" (memory_order.to_val memory_order.seq_cst)
        \arg "mo_failure" (memory_order.to_val memory_order.seq_cst)
        \pre{expected} expected_p |-> primR ty 1$m (Vinj ty expected)
        \pre{K} do_compare_exchange true this expected_p expected desired K
        \post{b}[Vbool b] K b.
    #[global] Hint Opaque compare_exchange_weak : sl_opacity.
    #[global] Arguments compare_exchange_weak : simpl never.
    Definition SpecFor_compare_exchange_weak := RegisterSpec compare_exchange_weak.
    #[global] Existing Instance SpecFor_compare_exchange_weak.

    Definition compare_exchange_weak_1 : mpred :=
      specify.template.method b0 "compare_exchange_weak" function_qualifiers.N "bool"
        [Tref ty; ty; Tmemory_order] $
        \this this
        \arg{expected_p} "o" (Vref expected_p)
        \arg{desired} "n" (Vinj ty desired)
        \arg "mo" (memory_order.to_val memory_order.seq_cst)
        \pre{expected} expected_p |-> primR ty 1$m (Vinj ty expected)
        \pre{K} do_compare_exchange true this expected_p expected desired K
        \post{b}[Vbool b] K b.
    #[global] Hint Opaque compare_exchange_weak_1 : sl_opacity.
    #[global] Arguments compare_exchange_weak_1 : simpl never.
    Definition SpecFor_compare_exchange_weak_1 := RegisterSpec compare_exchange_weak_1.
    #[global] Existing Instance SpecFor_compare_exchange_weak_1.

  End spec.

  Section bundled_spec.
    Context `{Σ : cpp_logic} {σ : genv}.
    Context (ty : type).
    Context `{!PrimVal ty A,!DefaultValue ty A}.

    Definition specs :=
      ctor ty **
      default_ctor ty **
      dtor ty **
      load ty **
      load_const ty **
      store ty    **
      assign ty   **
      cast ty     **
      exchange ty **
      compare_exchange_strong ty **
      compare_exchange_strong_1 ty **
      compare_exchange_weak ty **
      compare_exchange_weak_1 ty.
  End bundled_spec.

  Class UnOp (ty : type) (A : Type) (op_name : OverloadableOperator) :=
  { atomic_un_op : A -> A
  }.
  #[global] Hint Mode UnOp ! - ! : typeclass_instances.

  Class BinOp (ty1 ty2 : type) (A B : Type) (op_name : OverloadableOperator) (fun_name : ident) :=
  { atomic_bin_op : A -> B -> A
  }.
  #[global] Hint Mode BinOp ! - ! - ! - : typeclass_instances.
  #[global] Hint Mode BinOp ! - ! - - ! : typeclass_instances.

  Section with_ty.
    Context `{Σ : cpp_logic} {σ : genv}.
    Context (ty : type).
    Context `{PrimVal ty A}.

    #[local] Abbreviation s := (class_name ty) (only parsing).	(** [Atomic<T>] *)
    #[local] Abbreviation b1 := (base_name1 ty) (only parsing).
    #[local] Abbreviation bR q v := (_derived b1 s |-> R ty q v) (only parsing).

    (** Apply operation [op] to the atomic cell pointed by [this],
    and return the old contents to continuation [K]. *)
    #[local] Definition do_op (op : A -> A) (this : ptr) (K : A -> mpred) : mpred :=
      AC1 << ∀ m, this |-> bR 1$m m >> @ top, empty
          << this |-> bR 1$m (op m), COMM K m >>.
    #[global] Hint Opaque do_op : typeclass_instances sl_opacity.

    Section with_unop.
      Context `{UO : !UnOp ty A op_name}.

      (** Triple for unary operators that return the new value *)
      Definition unop_fetch : mpred :=
        specify.template.op b1 op_name function_qualifiers.N ty [] $
          \this this
          \pre{K} do_op (atomic_un_op (UnOp := UO)) this K
          \post{m}[Vinj ty (atomic_un_op (UnOp := UO) m)] K m.

      #[global] Hint Opaque unop_fetch : sl_opacity.
      #[global] Arguments unop_fetch : simpl never.
      Definition SpecFor_unop_fetch := RegisterSpec unop_fetch.
      #[global] Existing Instance SpecFor_unop_fetch.

      (** Triple for unary operators that return the old value *)
      Definition fetch_unop : mpred :=
        specify.template.op b1 op_name function_qualifiers.N ty [Tint] $
          \this this
          \arg{dummy} "dummy" (Vint dummy)
          \pre{K} do_op (atomic_un_op (UnOp := UO)) this K
          \post{m}[Vinj ty m] K m.

      #[global] Hint Opaque fetch_unop : sl_opacity.
      #[global] Arguments fetch_unop : simpl never.
      Definition SpecFor_fetch_unop := RegisterSpec fetch_unop.
      #[global] Existing Instance SpecFor_fetch_unop.
    End with_unop.

    Section with_binop.
      Context `{BO : !BinOp ty tyM A B op_name fun_name}.
      Context `{!PrimVal tyM B}.

      (** Triple for binary operators that return the new value *)
      Definition binop_fetch : mpred :=
        specify.template.op b1 op_name function_qualifiers.N ty [tyM] $
          \this this
          \arg{n : B} "v" (Vinj tyM n)
          \pre{K} do_op (flip (atomic_bin_op (BinOp := BO)) n) this K
          \post{m}[Vinj ty (atomic_bin_op (BinOp := BO) m n)] K m.
      #[global] Hint Opaque binop_fetch : sl_opacity.
      #[global] Arguments binop_fetch : simpl never.
      Definition SpecFor_binop_fetch := RegisterSpec binop_fetch.
      #[global] Existing Instance SpecFor_binop_fetch.

      (** Triple for methods that return the old value *)
      Definition fetch_binop : mpred :=
        specify.template.method b1 fun_name function_qualifiers.N ty [tyM; Tmemory_order] $
          \this this
          \arg{n : B} "v" (Vinj tyM n)
          \arg "mo" (memory_order.to_val memory_order.seq_cst)
          \pre{K} do_op (flip (atomic_bin_op (BinOp := BO)) n) this K
          \post{m}[Vinj ty m] K m.
      #[global] Hint Opaque fetch_binop : sl_opacity.
      #[global] Arguments fetch_binop : simpl never.
      Definition SpecFor_fetch_binop := RegisterSpec fetch_binop.
      #[global] Existing Instance SpecFor_fetch_binop.
    End with_binop.
  End with_ty.

  (** TODO fix overflow handling. *)
  Definition add_raw (sz : int_rank.t) (sgn : signed) (a b : Z) : Z :=
    if sgn is Signed then to_signed (int_rank.bitsize sz) (a + b)
    else to_unsigned (int_rank.bitsize sz) (a + b).

  #[global] Instance num_add {sz sgn} :
    BinOp (Tnum sz sgn) (Tnum sz sgn) Z Z OOPlusEqual "fetch_add" :=
  {| atomic_bin_op := add_raw sz sgn |}.
  (* TODO character types? *)

  (** TODO fix overflow handling. *)
  #[global] Instance num_sub {sz sgn} :
    BinOp (Tnum sz sgn) (Tnum sz sgn) Z Z OOMinusEqual "fetch_sub" :=
  {| atomic_bin_op a b := add_raw sz sgn a (-b) |}.

  #[global] Instance ptr_add {σ : genv} {ty} :
    BinOp (Tptr ty) Tptrdiff_t ptr Z OOPlusEqual "fetch_add" :=
  {| atomic_bin_op (p : ptr) b := p .[ ty ! b ] |}.

  #[global] Instance ptr_sub {σ : genv} {ty} :
    BinOp (Tptr ty) Tptrdiff_t ptr Z OOMinusEqual "fetch_sub" :=
  {| atomic_bin_op (p : ptr) b := p .[ ty ! -b ] |}.

End atomic_specs.

Include (atomic_specs atomic).
