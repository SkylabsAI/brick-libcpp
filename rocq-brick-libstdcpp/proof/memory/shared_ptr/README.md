# std::shared_ptr<T>

`shared_ptr` captures an idiom that encapsulates the destruction of objects
after the last reference to the object is destroyed. Idiomatically, we want to
support instances where clients should not need to think about when the
destruction occurs, i.e. this should not introduce case splitting in user
proofs. To address this, we aim to "pre-pay" for the destruction.

Like other abstractions within this library, the specifications of `shared_ptr`
are layered, meaning that we provide a low-level interface that encapsulates
relatively few details, but also provide higher-level interfaces for idiomatic
use cases.

While we often closely connect having a `shared_ptr` pointing to an object and
the ownership of the underlying object, in separation logic, we keep these
separate to "pass through" more powerful reasoning from the underlying ownership.

NOTE: Shared pointers are often used in larger contexts that often permit a
great deal of pointer structures, e.g. graphs and such. In these instances, it
may be necessary to use the lower-level interfaces to capture interesting
linkage between different objects and object types. Specifically, it is not clear
whether or not `std::weak_ptr` would get in the way of some of this reasoning.

## The Low-level Interface

The low-level interface breaks down into the following ownership and expresses
the operations using atomic commits in an very operational manner.

```coq
(** Ownership of the [shared_ptr] object carrying the pointer *)
Parameter R : gname -> cQp.t -> ptr -> Rep.
#[only(cfrac,cfracvalid,ascfractional,timeless)]

(** A reference to the underlying object.
    References can be combined according to the sum monoid and the sum
    of all of the <<n : N>> will be the current value of the referece count.

    The fractional nature of [ref] allows us to track all [ref], but it isn't
    clear if this is necessary. Why not simply use an auth-frag with the sum?
 *)
Parameter ref : gname -> Qp -> N -> mpred. (* fragmentary ownership *)
Parameter total_users : gname -> N -> mpred. (* authoritative ownership *)

(** The authority to hold [n] more references to the underlying object *)
Parameter contender (g : gname) (n : N) : mpred.
#[only(affine)] derive contender.

(* initializing constructor *)
cpp.spec "std::shared_ptr<T>::shared_ptr(T* )" with
  (\this this
   \arg{p} "p" (Vptr p)
   \post Exists g,
           this |-> shared_ptr.R g 1$m p **
           shared_ptr.contender g MAX)

(* copy ctor *)
cpp.spec "std::shared_ptr<T>::shared_ptr(std::shared_ptr<T>&)"
  (\this this
   \arg{other} "other" (Vref other)
   \pre{g PR qr qr' q p} other |-> shared_ptr.R g PR (qr + qr') q p
   \pre shared_ptr.contender g 1
   \post other |-> shared_ptr.R g PR qr q p **
         this |-> shared_ptr.R g PR qr' 1$m p).

(* destructor *)
cpp.spec "std::shared_ptr<T>::~shared_ptr()" with
  (\this this
   \pre{g PR qr} this |-> shared_ptr.R g PR qr 1$m p
   \pre PR qr
   \post shared_ptr.contender g 1).

(* <<use_count>>
   NOTE: this specification **might** work under two conditions:
   1. <<std::weak_ptr>>s do not exist.
   2. the access on the counter was not weak.
   More thinking is necessary to understand if these can be relaxed, the second
   seems to make this very subtle.
*)
cpp.spec "std::shared_ptr<T>::use_count() const" with
  (\this this
   \let{cnst} q := cQp.mk 1 cnst
   \pre{g PR qr cnst} this |-> shared_ptr.R g PR qr q p
   \post{count}[Vint count]
      if bool_decide (count = 0) then
        [| p = nullptr |] ** this |-> shared_ptr.R g PR qr q nullptr
      else if bool_decide (count = 1) then
        default (1 - qr)%Qp emp PR **
        this |-> shared_ptr.R g PR 1 q q p
      else this |-> shared_ptr.R g PR qr q p).
```

## Client-Retained Ownership

In this interface, the client retains ownership of the object that the
shared_ptr points to.

```coq
(** [R g PR qr q p] represents the shared pointer ownership combined with the
    justification that the object can be destroyed using ownership [PR 1].

    1. The constructor initializes [qr] with 1 meaning that (at least) [PR 1]
       is still owned by the client.
    2. When copying a shared_ptr, the [qr] is split between the old and new
       objects preserving the amount that is usable by the client.
    3. When destroying a shared_ptr, the <<PR qr>> is returned to the shared_ptr
       abstraction and a [contender] token is returned to the caller.

    The [PR] ownership that is returned to the client are effectively lost forever;
    however, because <<PR>> can be split arbitrarily it is always possible to get
    more pieces by splitting the component that you have. The downside to this is
    that you end up with highly non-uniform fractions.
 *)
Parameter R : gname -> (Qp -> Rep) -> Qp -> cQp.t -> ptr -> Rep.

(** same as in the low-level interface *)
Parameter contender (g : gname) (n : N) : mpred.

(** permits weakening of <<PR>>, this is subtle and might not be necessary *)
Axiom R_weaken : forall g PR PR' qr q p (_ : Fractional PR'),
 (Forall q, PR' q -* PR q) |-- R g PR qr q p -* R g PR' qr q p.

(* initializing constructor *)
cpp.spec "std::shared_ptr<T>::shared_ptr(T* )" with
  (\this this
   \arg{p} "p" (Vptr p)
   \require{(PR : Qp -> Rep)} Fractional PR
   \pre (PR 1 -* wp_delete "$T" p emp) (* <-- pre-pay for the de-allocation. In most cases, this should be trivial to discharge *)
   \post Exists g,
           this |-> shared_ptr.R g PR 1%Qp 1$m p
           shared_ptr.contender g MAX)

(* copy ctor *)
cpp.spec "std::shared_ptr<T>::shared_ptr(std::shared_ptr<T>&)"
  (\this this
   \arg{other} "other" (Vref other)
   \pre{g PR qr qr' q p} other |-> shared_ptr.R g PR (qr + qr') q p
   \pre shared_ptr.contender g 1
   \post other |-> shared_ptr.R g PR qr q p **
         this |-> shared_ptr.R g PR qr' 1$m p).

(* destructor *)
cpp.spec "std::shared_ptr<T>::~shared_ptr()" with
  (\this this
   \pre{g PR qr} this |-> shared_ptr.R g PR qr 1$m p
   \pre PR qr
   \post shared_ptr.contender g 1).

(* <<use_count>>
   NOTE: this specification **might** work under two conditions:
   1. <<std::weak_ptr>>s do not exist.
   2. the access on the counter was not weak.
   More thinking is necessary to understand if these can be relaxed, the second
   seems to make this very subtle.
*)
cpp.spec "std::shared_ptr<T>::use_count() const" with
  (\this this
   \let{cnst} q := cQp.mk 1 cnst
   \pre{g PR qr cnst} this |-> shared_ptr.R g PR qr q p
   \post{count}[Vint count]
      if bool_decide (count = 0) then
        [| p = nullptr |] ** this |-> shared_ptr.R g PR qr q nullptr
      else if bool_decide (count = 1) then
        default (1 - qr)%Qp emp PR **
        this |-> shared_ptr.R g PR 1 q q p
      else this |-> shared_ptr.R g PR qr q p).
```

## Asymmetric Ownership

In this specification, the full ownership of the object is transferred the
`shared_ptr` library and it is taken out each time that a new `shared_ptr` is
created. In practice, the assymetric nature is probably only useful for the
array form when different clients will get access to different elements.

This specification is based on: ...

```coq



```
