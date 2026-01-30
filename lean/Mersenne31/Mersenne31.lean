
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import Mersenne31.HaxPatch
open HaxPatch
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace Mersenne31.Unimplemented

--  Dummy `Iterator` placeholder trait
class Iterator.AssociatedTypes (Self : Type) where
  Item : Type

attribute [reducible] Iterator.AssociatedTypes.Item

abbrev Iterator.Item :=
  Iterator.AssociatedTypes.Item

class Iterator (Self : Type)
  [associatedTypes : outParam (Iterator.AssociatedTypes (Self : Type))]
  where

--  Copied `Sum` trait
class Sum.AssociatedTypes (Self : Type) (A : Type) where

class Sum (Self : Type) (A : Type)
  [associatedTypes : outParam (Sum.AssociatedTypes (Self : Type) (A : Type))]
  where
  sum (Self) (A)
    (I : Type)
    [trait_constr_sum_associated_type_i1 : Iterator.AssociatedTypes I]
    [trait_constr_sum_i1 : Iterator
      I
      (associatedTypes := {
        show Iterator.AssociatedTypes I
        by infer_instance
        with Item := A})] :
    (I -> RustM Self)

--  Copied `Product` trait
class Product.AssociatedTypes (Self : Type) (A : Type) where

class Product (Self : Type) (A : Type)
  [associatedTypes : outParam (Product.AssociatedTypes (Self : Type) (A :
      Type))]
  where
  product (Self) (A)
    (I : Type)
    [trait_constr_product_associated_type_i1 : Iterator.AssociatedTypes I]
    [trait_constr_product_i1 : Iterator
      I
      (associatedTypes := {
        show Iterator.AssociatedTypes I
        by infer_instance
        with Item := A})] :
    (I -> RustM Self)

end Mersenne31.Unimplemented


namespace Mersenne31.Mersenne31

--  The Mersenne31 prime
def P : u32 :=
  RustM.of_isOk (do ((← ((1 : u32) <<<? (31 : i32))) -? (1 : u32))) (by rfl)

--  The Mersenne31 prime as u64 to avoid casting `P`
def P64 : u64 :=
  RustM.of_isOk (do ((← ((1 : u64) <<<? (31 : i32))) -? (1 : u64))) (by rfl)

--  The prime field `F_p` where `p = 2^31 - 1`.
structure Mersenne31 where
  value : u32

@[instance] opaque Impl_14.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes Mersenne31 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_14 :
  Core_models.Clone.Clone Mersenne31 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_13.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes Mersenne31 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_13 :
  Core_models.Marker.Copy Mersenne31 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_15.AssociatedTypes :
  Core_models.Default.Default.AssociatedTypes Mersenne31 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_15 :
  Core_models.Default.Default Mersenne31 :=
  by constructor <;> exact Inhabited.default

--  Create a new field element from any `u32`.
-- 
--  Any `u32` value is accepted and automatically reduced modulo P.
def Impl.new (value : u32) : RustM Mersenne31 := do
  (pure (Mersenne31.mk (value := (← (value %? P)))))

--  Create a field element from a value assumed to be < 2^31.
-- 
--  # Safety
--  The element must lie in the range: `[0, 2^31 - 1]`.
def Impl.new_reduced (value : u32) : RustM Mersenne31 := do
  let _ ←
    (Hax_lib.assert
      (← (Rust_primitives.Hax.Machine_int.eq
        (← (value >>>? (31 : i32)))
        (0 : u32))));
  (pure (Mersenne31.mk (value := value)))

--  Convert a u32 element into a Mersenne31 element.
-- 
--  Returns `None` if the element does not lie in the range: `[0, 2^31 - 1]`.
def Impl.new_checked (value : u32) :
    RustM (Core_models.Option.Option Mersenne31) := do
  if
  (← (Rust_primitives.Hax.Machine_int.eq (← (value >>>? (31 : i32))) (0 : u32)))
  then
    (pure (Core_models.Option.Option.Some (Mersenne31.mk (value := value))))
  else
    (pure Core_models.Option.Option.None)

--  NOTE: Placeholder dummy impl
@[reducible] instance Impl_11.AssociatedTypes :
  Mersenne31.Unimplemented.Sum.AssociatedTypes Mersenne31 Mersenne31
  where

instance Impl_11 : Mersenne31.Unimplemented.Sum Mersenne31 Mersenne31 where
  sum :=
    fun
      (I : Type)
      [trait_constr_sum_associated_type_i0 :
        Mersenne31.Unimplemented.Iterator.AssociatedTypes
        I]
      [trait_constr_sum_i0 : Mersenne31.Unimplemented.Iterator
        I
        (associatedTypes := {
          show Mersenne31.Unimplemented.Iterator.AssociatedTypes I
          by infer_instance
          with Item := Mersenne31})] (iter : I) => do
    (Impl.new (0 : u32))

--  NOTE: Placeholder dummy impl. Unclear atm where the source is.
@[reducible] instance Impl_12.AssociatedTypes :
  Mersenne31.Unimplemented.Product.AssociatedTypes Mersenne31 Mersenne31
  where

instance Impl_12 : Mersenne31.Unimplemented.Product Mersenne31 Mersenne31 where
  product :=
    fun
      (I : Type)
      [trait_constr_product_associated_type_i0 :
        Mersenne31.Unimplemented.Iterator.AssociatedTypes
        I]
      [trait_constr_product_i0 : Mersenne31.Unimplemented.Iterator
        I
        (associatedTypes := {
          show Mersenne31.Unimplemented.Iterator.AssociatedTypes I
          by infer_instance
          with Item := Mersenne31})] (iter : I) => do
    (Impl.new (0 : u32))

end Mersenne31.Mersenne31


namespace Mersenne31.Field

--  NOTE: DUMMY PLACEHOLDER. Missing `PrimeField`
--  A prime field `ℤ/p` with order, `p < 2^64`.
class PrimeField64.AssociatedTypes (Self : Type) where

class PrimeField64 (Self : Type)
  [associatedTypes : outParam (PrimeField64.AssociatedTypes (Self : Type))]
  where
  ORDER_U64 (Self) : u64
  as_canonical_u64 (Self) : (Self -> RustM u64)
  to_unique_u64 (Self) (self : Self) :RustM u64 := do
    (as_canonical_u64 self)

--  NOTE: DUMMY PLACEHOLDER. Missing `PrimeField` and `PrimeField64`
--  NOTE: `PrimeField64` supertrait removed to avoid circularities in the implementation
--  A prime field `ℤ/p` with order `p < 2^32`.
class PrimeField32.AssociatedTypes (Self : Type) where

class PrimeField32 (Self : Type)
  [associatedTypes : outParam (PrimeField32.AssociatedTypes (Self : Type))]
  where
  ORDER_U32 (Self) : u32
  as_canonical_u32 (Self) : (Self -> RustM u32)
  to_unique_u32 (Self) (self : Self) :RustM u32 := do
    (as_canonical_u32 self)

--  NOTE: Removed the equality constraint of associated type for supertraits
class PrimeCharacteristicRing.AssociatedTypes (Self : Type) where
  [trait_constr_PrimeCharacteristicRing_i0 :
  Core_models.Default.Default.AssociatedTypes
  Self]
  [trait_constr_PrimeCharacteristicRing_i1 :
  Core_models.Clone.Clone.AssociatedTypes
  Self]
  [trait_constr_PrimeCharacteristicRing_i2 :
  Core_models.Ops.Arith.Add.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i3 :
  Core_models.Ops.Arith.AddAssign.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i4 :
  Core_models.Ops.Arith.Sub.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i5 :
  Core_models.Ops.Arith.SubAssign.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i6 :
  Core_models.Ops.Arith.Neg.AssociatedTypes
  Self]
  [trait_constr_PrimeCharacteristicRing_i7 :
  Core_models.Ops.Arith.Mul.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i8 :
  Core_models.Ops.Arith.MulAssign.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i9 :
  Mersenne31.Unimplemented.Sum.AssociatedTypes
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i10 :
  Mersenne31.Unimplemented.Product.AssociatedTypes
  Self
  Self]
  PrimeSubfield : Type

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i0

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i1

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i2

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i3

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i4

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i5

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i6

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i7

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i8

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i9

attribute [instance]
  PrimeCharacteristicRing.AssociatedTypes.trait_constr_PrimeCharacteristicRing_i10

attribute [reducible] PrimeCharacteristicRing.AssociatedTypes.PrimeSubfield

abbrev PrimeCharacteristicRing.PrimeSubfield :=
  PrimeCharacteristicRing.AssociatedTypes.PrimeSubfield

class PrimeCharacteristicRing (Self : Type)
  [associatedTypes : outParam (PrimeCharacteristicRing.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr_PrimeCharacteristicRing_i0 : Core_models.Default.Default Self]
  [trait_constr_PrimeCharacteristicRing_i1 : Core_models.Clone.Clone Self]
  [trait_constr_PrimeCharacteristicRing_i2 :
  Core_models.Ops.Arith.Add
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i3 :
  Core_models.Ops.Arith.AddAssign
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i4 :
  Core_models.Ops.Arith.Sub
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i5 :
  Core_models.Ops.Arith.SubAssign
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i6 : Core_models.Ops.Arith.Neg Self]
  [trait_constr_PrimeCharacteristicRing_i7 :
  Core_models.Ops.Arith.Mul
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i8 :
  Core_models.Ops.Arith.MulAssign
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i9 :
  Mersenne31.Unimplemented.Sum
  Self
  Self]
  [trait_constr_PrimeCharacteristicRing_i10 :
  Mersenne31.Unimplemented.Product
  Self
  Self]
  ZERO (Self) : Self
  ONE (Self) : Self
  TWO (Self) : Self
  NEG_ONE (Self) : Self
  from_prime_subfield (Self) : (associatedTypes.PrimeSubfield -> RustM Self)
  from_bool (Self) (b : Bool) :RustM Self := do
    if b then ONE else ZERO
  double (Self)
    (A : Type)
    [trait_constr_double_associated_type_i1 :
      Core_models.Clone.Clone.AssociatedTypes
      A]
    [trait_constr_double_i1 : Core_models.Clone.Clone A ]
    [trait_constr_double_associated_type_i2 :
      Core_models.Ops.Arith.Add.AssociatedTypes
      A
      A]
    [trait_constr_double_i2 : Core_models.Ops.Arith.Add A A ] (a : A) :RustM
    (Core_models.Ops.Arith.Add.Output A A) := do
    (Core_models.Ops.Arith.Add.add
      A
      A
      (← (Core_models.Clone.Clone.clone A a))
      (← (Core_models.Clone.Clone.clone A a)))

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i0

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i1

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i2

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i3

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i4

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i5

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i6

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i7

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i8

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i9

attribute [instance]
  PrimeCharacteristicRing.trait_constr_PrimeCharacteristicRing_i10

end Mersenne31.Field


namespace Mersenne31.Mersenne31

--  NOTE: Dummy implementation of a dummy trait
@[reducible] instance Impl_3.AssociatedTypes :
  Mersenne31.Field.PrimeField32.AssociatedTypes Mersenne31
  where

instance Impl_3 : Mersenne31.Field.PrimeField32 Mersenne31 where
  ORDER_U32 := P
  as_canonical_u32 := fun (self : Mersenne31) => do
    if
    (← (Rust_primitives.Hax.Machine_int.eq
      (Mersenne31.value self) P)) then
      (pure (0 : u32))
    else
      (pure (Mersenne31.value self))

--  NOTE: Dummy implementation of a dummy trait
@[reducible] instance Impl_2.AssociatedTypes :
  Mersenne31.Field.PrimeField64.AssociatedTypes Mersenne31
  where

instance Impl_2 : Mersenne31.Field.PrimeField64 Mersenne31 where
  ORDER_U64 := P64
  as_canonical_u64 := fun (self : Mersenne31) => do
    (Core_models.Convert.Into.into
      u32
      u64 (← (Mersenne31.Field.PrimeField32.as_canonical_u32 Mersenne31 self)))

@[reducible] instance Impl_4.AssociatedTypes :
  Core_models.Ops.Arith.Add.AssociatedTypes Mersenne31 Mersenne31
  where
  Output := Mersenne31

instance Impl_4 : Core_models.Ops.Arith.Add Mersenne31 Mersenne31 where
  add := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let ⟨sum_i32, over⟩ ←
      (Core_models.Num.Impl_2.overflowing_add
        (← (Rust_primitives.Hax.cast_op (Mersenne31.value self)))
        (← (Rust_primitives.Hax.cast_op (Mersenne31.value rhs))));
    let sum_u32 : u32 ← (Rust_primitives.Hax.cast_op sum_i32);
    let sum_corr : u32 ←
      (Core_models.Num.Impl_8.wrapping_sub
        sum_u32
        (← (Mersenne31.Field.PrimeField32.ORDER_U32 Mersenne31)));
    (Impl.new_reduced (← if over then (pure sum_corr) else (pure sum_u32)))

@[reducible] instance Impl_5.AssociatedTypes :
  Core_models.Ops.Arith.Sub.AssociatedTypes Mersenne31 Mersenne31
  where
  Output := Mersenne31

instance Impl_5 : Core_models.Ops.Arith.Sub Mersenne31 Mersenne31 where
  sub := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let ⟨sub, over⟩ ←
      (Core_models.Num.Impl_8.overflowing_sub
        (Mersenne31.value self)
        (Mersenne31.value rhs));
    let sub : u32 ← (sub -? (← (@Rust_primitives.Hax.cast_op Bool u32 _ over)));
    (Impl.new_reduced
      (← (sub &&&? (← (Mersenne31.Field.PrimeField32.ORDER_U32 Mersenne31)))))

@[reducible] instance Impl_6.AssociatedTypes :
  Core_models.Ops.Arith.Neg.AssociatedTypes Mersenne31
  where
  Output := Mersenne31

instance Impl_6 : Core_models.Ops.Arith.Neg Mersenne31 where
  neg := fun (self : Mersenne31) => do
    (Impl.new_reduced
      (← ((Mersenne31.Field.PrimeField32.ORDER_U32 Mersenne31)
        -? (Mersenne31.value self))))

@[reducible] instance Impl_8.AssociatedTypes :
  Core_models.Ops.Arith.AddAssign.AssociatedTypes Mersenne31 Mersenne31
  where

instance Impl_8 : Core_models.Ops.Arith.AddAssign Mersenne31 Mersenne31 where
  add_assign := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let self : Mersenne31 ←
      (Core_models.Ops.Arith.Add.add Mersenne31 Mersenne31 self rhs);
    (pure self)

@[reducible] instance Impl_9.AssociatedTypes :
  Core_models.Ops.Arith.SubAssign.AssociatedTypes Mersenne31 Mersenne31
  where

instance Impl_9 : Core_models.Ops.Arith.SubAssign Mersenne31 Mersenne31 where
  sub_assign := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let self : Mersenne31 ←
      (Core_models.Ops.Arith.Sub.sub Mersenne31 Mersenne31 self rhs);
    (pure self)

def from_u62 (input : u64) : RustM Mersenne31 := do
  let _ ←
    (Hax_lib.assert
      (← (Rust_primitives.Hax.Machine_int.lt
        input
        (← ((1 : u64) <<<? (62 : i32))))));
  let input_lo : u32 ←
    (Rust_primitives.Hax.cast_op
      (← (input &&&? (← ((← ((1 : u64) <<<? (31 : i32))) -? (1 : u64))))));
  let input_high : u32 ←
    (Rust_primitives.Hax.cast_op (← (input >>>? (31 : i32))));
  (Core_models.Ops.Arith.Add.add
    Mersenne31
    Mersenne31
    (← (Impl.new_reduced input_lo))
    (← (Impl.new_reduced input_high)))

@[reducible] instance Impl_7.AssociatedTypes :
  Core_models.Ops.Arith.Mul.AssociatedTypes Mersenne31 Mersenne31
  where
  Output := Mersenne31

instance Impl_7 : Core_models.Ops.Arith.Mul Mersenne31 Mersenne31 where
  mul := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let prod : u64 ←
      ((← (Core_models.Convert.From._from u64 u32 (Mersenne31.value self)))
        *? (← (Core_models.Convert.From._from u64 u32 (Mersenne31.value rhs))));
    (from_u62 prod)

@[reducible] instance Impl_10.AssociatedTypes :
  Core_models.Ops.Arith.MulAssign.AssociatedTypes Mersenne31 Mersenne31
  where

instance Impl_10 : Core_models.Ops.Arith.MulAssign Mersenne31 Mersenne31 where
  mul_assign := fun (self : Mersenne31) (rhs : Mersenne31) => do
    let self : Mersenne31 ←
      (Core_models.Ops.Arith.Mul.mul Mersenne31 Mersenne31 self rhs);
    (pure self)

@[reducible] instance Impl_1.AssociatedTypes :
  Mersenne31.Field.PrimeCharacteristicRing.AssociatedTypes Mersenne31
  where
  PrimeSubfield := Mersenne31

instance Impl_1 : Mersenne31.Field.PrimeCharacteristicRing Mersenne31 where
  ZERO := RustM.of_isOk (do (Mersenne31.mk (value := (0 : u32)))) (by rfl)
  ONE := RustM.of_isOk (do (Mersenne31.mk (value := (1 : u32)))) (by rfl)
  TWO := RustM.of_isOk (do (Mersenne31.mk (value := (2 : u32)))) (by rfl)
  NEG_ONE := RustM.of_isOk
    (do
    (Mersenne31.mk
      (value := (← ((Mersenne31.Field.PrimeField32.ORDER_U32 Mersenne31)
        -? (1 : u32))))))
    (by rfl)
  from_prime_subfield := fun (f : Mersenne31) => do (pure f)
  from_bool := fun (b : Bool) => do
    (Impl.new_reduced (← (Rust_primitives.Hax.cast_op b)))

--  Convert a `[u32; N]` array to an array of field elements.
-- 
--  Const version of `input.map(Mersenne31::new)`.
def Impl.new_array (N : usize) (input : (RustArray u32 N)) :
    RustM (RustArray Mersenne31 N) := do
  let output : (RustArray Mersenne31 N) ←
    (Rust_primitives.Hax.repeat
      (← (Mersenne31.Field.PrimeCharacteristicRing.ZERO Mersenne31))
      N);
  let i : usize := (0 : usize);
  let ⟨i, output⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, output⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, output⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i N) : RustM Bool))
      (fun ⟨i, output⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i output)
      (fun ⟨i, output⟩ =>
        (do
        let output : (RustArray Mersenne31 N) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            output
            i
            {(← output[i]_?) with value := (← ((← input[i]_?) %? P))});
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i output)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray Mersenne31 N)))));
  (pure output)

end Mersenne31.Mersenne31

