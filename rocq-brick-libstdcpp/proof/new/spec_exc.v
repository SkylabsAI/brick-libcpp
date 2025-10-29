Require Import bluerock.auto.cpp.specs.

Require Import bluerock.brick.libstdcpp.new.inc_new_cpp.
Require Export bluerock.brick.libstdcpp.new.spec.

Import cpp_notation.

(** This file provides a specification of the default <<operator new(size_t)>>
    provided by the C++ standard library. This function communicates allocation
    failures using exceptions which BRiCk does not currently support.

    A common way to make this specification sound is to modify the
    implementation of <<operator new>> to abort on allocation, e.g. by calling
    <<exit(1);>>. With this revision, the following [new_spec] is sound.

    If you require the use of exceptions in your development,
    please up-vote this feature request:
    <<https://github.com/bluerock-io/BRiCk/issues/15>>.
 *)


#[local] Set Primitive Projections.

Section with_cpp.
  Context `{Σ : cpp_logic, module ⊧ σ}.

  (** <<operator new(size_t)>> is not allowed to return <<nullptr>>, it
      signals failure by raising an exception.
   *)
  cpp.spec "operator new(size_t)" as new_spec with
      (\arg{sz} "sz"      (Vn sz)
       \post{p}[Vptr p] p |-> (blockR sz 1$m **
                               nonnullR **
                               alignedR STDCPP_DEFAULT_NEW_ALIGNMENT **
                               allocatedR 1 sz)).

  cpp.spec "operator new[](size_t)" as operator_new_array with
      (\arg{sz} "sz" (Vn sz)
       \post{p}[Vptr p]
           p |-> (blockR sz 1$m **
                  nonnullR **
                  alignedR STDCPP_DEFAULT_NEW_ALIGNMENT **
                  allocatedR 1 sz)).

End with_cpp.
