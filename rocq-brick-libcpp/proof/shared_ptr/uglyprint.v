Require Import bluerock.auto.cpp.proof.

(*
The type `name` in Coq comes from cpp semantics in this file. it is a complicated mutual inductive. It has a custom parsing notation.
It seems there is no way to disable the notation for printing.
So, it is hard to see the structure of a `name` shown as string, as  `fo` above.
So your task is write an ugly printier for `name`. it should not prettify but eluciadte the actual structure (the inductive constructors)

*)
 (* We want PrimString literals and [cat]/[++] in scope *)
Open Scope pstring_scope.

(* Hook up the existing implementations *)
Definition type_to_string : type → PrimString.string := pretty.printT.
Definition expr_to_string : Expr → PrimString.string := pretty.printE.
Definition fq_to_string : function_qualifiers.t → PrimString.string := pretty.printFQ.
Definition op_to_string : OverloadableOperator → PrimString.string := pretty.printOO.
Definition N_to_string : N → PrimString.string := N.to_string.

(* A generic printer for lists *)
Definition print_list {A} (f:A->PrimString.string) (l:list A) : PrimString.string :=
  let fix go xs :=
    match xs with
    | [] => ""
    | y::ys => cat "," (cat (f y) (go ys))
    end in
  match l with
  | [] => "[]"
  | x::xs => cat "[" (cat (f x) (cat (go xs) "]"))
  end.

(* Printer for the atomic_name_ type *)
Definition atomic_name_to_string (an:atomic_name) : PrimString.string :=
  match an with
  | Nid id =>
      cat "Nid(" (cat id ")")
  | Nfunction fq id tys =>
      cat "Nfunction("
        (cat (fq_to_string fq)
         (cat "," (cat id (cat "," (cat (print_list type_to_string tys) ")")))))
  | Nctor tys =>
      cat "Nctor(" (cat (print_list type_to_string tys) ")")
  | Ndtor => "Ndtor"
  | Nop fq op tys =>
      cat "Nop("
        (cat (fq_to_string fq)
         (cat "," (cat (op_to_string op)
                  (cat "," (cat (print_list type_to_string tys) ")")))))
  | Nop_conv fq t =>
      cat "Nop_conv("
        (cat (fq_to_string fq)
         (cat "," (cat (type_to_string t) ")")))
  | Nop_lit id tys =>
      cat "Nop_lit("
        (cat id (cat "," (cat (print_list type_to_string tys) ")")))
  | Nanon n =>
      cat "Nanon(" (cat (N_to_string n) ")")
  | Nanonymous => "Nanonymous"
  | Nfirst_decl id =>
      cat "Nfirst_decl(" (cat id ")")
  | Nfirst_child id =>
      cat "Nfirst_child(" (cat id ")")
  | Nunsupported_atomic s =>
      cat "Nunsupported_atomic(" (cat s ")")
  end.

(* Mutual printer for name and temp_arg *)
Fixpoint name_to_string (n:name) : PrimString.string :=
  match n with
  | Ninst n0 args =>
      cat "Ninst("
        (cat (name_to_string n0)
         (cat "," (cat (print_list temp_arg_to_string args) ")")))
  | Nglobal an =>
      cat "Nglobal(" (cat (atomic_name_to_string an) ")")
  | Ndependent t =>
      cat "Ndependent(" (cat (type_to_string t) ")")
  | Nscoped n0 an =>
      cat "Nscoped("
        (cat (name_to_string n0)
         (cat "," (cat (atomic_name_to_string an) ")")))
  | Nunsupported s =>
      cat "Nunsupported(" (cat s ")")
  end

with temp_arg_to_string (a:temp_arg) : PrimString.string :=
  match a with
  | Atype t =>
      cat "Atype(" (cat (type_to_string t) ")")
  | Avalue e =>
      cat "Avalue(" (cat (expr_to_string e) ")")
  | Apack lst =>
      cat "Apack(" (cat (print_list temp_arg_to_string lst) ")")
  | Atemplate nm =>
      cat "Atemplate(" (cat (name_to_string nm) ")")
  | Aunsupported s =>
      cat "Aunsupported(" (cat s ")")
  end.
