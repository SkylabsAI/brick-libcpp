Require Import bluerock.auto.cpp.specs.
Require Export bluerock.brick.libstdcpp.new.pred.
Require Import bluerock.brick.libstdcpp.new.inc_new_cpp.

#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, source ⊧ σ}.

  cpp.spec "operator new(std::size_t, const std::nothrow_t&)" as operator_new_nothrow with
    (\arg{sz}        "sz"      (Vn sz)
     \arg{nothrow_p} "nothrow" (Vref nothrow_p)
     \post{p}[Vptr p]
        if bool_decide (p = nullptr) then emp
        else p |-> (blockR sz 1$m **
                    alignedR STDCPP_DEFAULT_NEW_ALIGNMENT **
                    allocatedR 1 sz)).

  (* Consult <<spec_exc.v>> for a specification of <<operator new(size_t)>>, the
     "default" <<new>>.
   *)

  cpp.spec "operator delete(void*)" as operator_delete with
      (\arg{p} "p" (Vptr p)
       \pre if bool_decide (p = nullptr) then emp
            else ∃ sz, p |-> (allocatedR 1 sz ** blockR sz 1$m)
       \post emp).

(*  #[ignore_missing] *)
  cpp.spec "operator delete(void*, std::size_t, enum std::align_val_t)" as operator_delete_size_align with
      (\arg{p} "p" (Vptr p)
       \arg{sz} "sz" (Vn sz)
       \arg{al} "al" (Vn al)
       \pre if bool_decide (p = nullptr) then emp
            else ∃ sz, p |-> (allocatedR 1 sz ** blockR sz 1$m ** alignedR al)
       \post emp).

(*  #[ignore_missing] *)
  cpp.spec "operator delete(void*, std::size_t)" as operator_delete_size with
      (\arg{p} "p" (Vptr p)
       \arg{sz} "sz" (Vn sz)
       \pre if bool_decide (p = nullptr) then emp
            else p |-> (allocatedR 1 sz ** blockR sz 1$m)
       \post emp).

  (** ** Array <<new>> and <<delete>> *)
  cpp.spec "operator new[](std::size_t, const std::nothrow_t&)" as operator_new_array_nothrow with
      (\arg{sz} "sz" (Vn sz)
       \arg{nothrow_p} "" (Vptr nothrow_p)
       \post{p}[Vptr p]
          if bool_decide (p = nullptr) then emp
          else p |-> (blockR sz 1$m **
                      alignedR STDCPP_DEFAULT_NEW_ALIGNMENT **
                      allocatedR 1 sz)).

  cpp.spec "operator delete[](void*)" as operator_delete_array with
      (\arg{p} "p" (Vptr p)
       \pre if bool_decide (p = nullptr) then emp
            else ∃ sz, p |-> (allocatedR 1 sz ** blockR sz 1$m)
       \post emp).

  cpp.spec "operator delete[](void*, std::size_t)" as operator_delete_array_size with
      (\arg{p} "p" (Vptr p)
       \arg{sz} "sz" (Vn sz)
       \pre  if bool_decide (p = nullptr) then emp
             else p |-> (allocatedR 1 sz ** blockR sz 1$m)
       \post emp).

End with_cpp.

NES.Begin alloc.

  (* TODO: fix this *)
  Notation interface := (operator_new_nothrow ** operator_delete ** valid_ptr (_global "nothrow")).
NES.End alloc.

#[global] Hint Extern 1000 (SpecFor "operator new(unsigned long)"%cpp_name _) =>
   (idtac "<<operator new(size_t)>>'s specification requires exceptions."
          "See [bluerock.brick.libstdcpp.new.spec_exc] for more information about it.";
    exact (SpecFor.mk _ emp)) : typeclass_instances.

#[global] Hint Extern 1000 (SpecFor "operator new[](unsigned long)"%cpp_name _) =>
  (idtac "<<operator new[](size_t)>>'s specification requires exceptions."
     "See [bluerock.brick.libstdcpp.new.spec_exc] for more information about it.";
   exact (SpecFor.mk _ emp)) : typeclass_instances.
