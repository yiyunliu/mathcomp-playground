From mathcomp
       Require Import ssreflect ssrbool ssrnat eqtype ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SemigroupDef.

  Record mixin_of (T : Type) :=
    Mixin { op : T -> T -> T
          ; _ : associative op }.

  Definition mixin_of_nat : mixin_of nat.
  Proof.
    apply Mixin with (op := Nat.add).
    rewrite /associative.
    apply : PeanoNat.Nat.add_assoc.
  Defined.

  Section Packing.

    Structure pack_type : Type := Pack {type : Type; _ : mixin_of type}.

    Definition nat_add_packed : pack_type.
      eauto using mixin_of_nat, pack_type.
    Defined.

    Fail Check 1 : nat_add_packed.
    (* The function that witnesses the coercion : the type on which
    the function will be automatically applied *)
    Local Coercion type : pack_type >-> Sortclass.

    Check 1 : nat_add_packed.
    (* The reason why the above Check works is because the local
    coercion replaces nat_add_packed with type (nat_add_packed) *)
    Check 1 : type (nat_add_packed).


    Variable cT: pack_type.
    (* Project out the mixin instance from the package *)
    Definition semigroup_struct : mixin_of cT.
      case : cT => //.
    Defined.

    Definition addop := op semigroup_struct.

  End Packing.

  Check addop.

  Module Exports.
    (* e.g. a tuple of nat and its methods *)
    Notation semigroup := pack_type.
    (* Constructor of mixin_of *)
    Notation SemigroupMixin := Mixin.
    (* Constructor of the pack_type *)
    Notation Semigroup T m := (@Pack T m).
    (* The operator *)
    Notation "x \+ y" := (addop x y) (at level 43, left associativity).
    (* Why can we write addop as if it is binary? Because we set the argument as implicit from earlier *)
    Check type.
    Coercion type : pack_type >-> Sortclass.

    Section SemigroupLemmas.
      Variable U : semigroup.
      (* lemmas... *)
    End SemigroupLemmas.

  End Exports.


End SemigroupDef.

(* If you import the current file ("mathstruct.v"), you'd only be able
to see the stuff mentioned in the Exports submodule *)
Export SemigroupDef.Exports.


Module MonoidDef.
  Record mixin_of (U : semigroup) :=
    Mixin { unit_op : U
          ; _ : forall a, unit_op \+ a = a
          ; _ : forall a, a \+ unit_op = a  }.

  Structure pack_type : Type := Pack {semigroupT : semigroup; _ : mixin_of semigroupT}.

  Module Exports.
    Notation monoid := pack_type.
    Notation MonoidMixin := Mixin.
    Notation Monoid T m := (@Pack T m).
    Coercion semigroupT : pack_type >-> semigroup.
    Section MonoidLemmas.
      Variable U : monoid.
    End MonoidLemmas.
  End Exports.
End MonoidDef.
