Require Import bluerock.auto.cpp.specs.

Require Import bluerock.cpp.stdlib.new.inc_new_cpp.
Require Import bluerock.cpp.stdlib.new.spec.

Import cpp_notation.


#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, module ⊧ σ}.


  (** This stdlib function communicates allocation failures using exceptions. Because the BRiCk semantics doesnt support exceptions yet, we assume that allocation failures never happen. Only use this spec in places where you dont care what happens after a dynamic allocation failure. Even when the exception is unhandled, it can execute arbitrary code before exiting, e.g. due to stack unwinding. It may make sense to wrap the default implementation in a function that catches the exception and does exit(1) right away, to ensure that the stack unwinding code doesnt do anything worse than exiting. *)
  cpp.spec "operator new[](size_t)" as operator_new_array with
      (\arg{sz} "sz" (Vn sz)
       \post{p}[Vptr p]
          p |-> (blockR sz 1$m **
                   nonnullR **
                   alignedR STDCPP_DEFAULT_NEW_ALIGNMENT **
                   allocatedR 1 sz)).

End with_cpp.
