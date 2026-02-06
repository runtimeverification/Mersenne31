
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


namespace Mersenne31.Monty_31

--  MontyParameters contains the prime P along with constants needed to convert elements into and out of MONTY form.
--  The MONTY constant is assumed to be a power of 2.
class MontyParameters.AssociatedTypes (Self : Type) where
  [trait_constr_MontyParameters_i0 :
  Core_models.Marker.Copy.AssociatedTypes
  Self]

attribute [instance]
  MontyParameters.AssociatedTypes.trait_constr_MontyParameters_i0

class MontyParameters (Self : Type)
  [associatedTypes : outParam (MontyParameters.AssociatedTypes (Self : Type))]
  where
  [trait_constr_MontyParameters_i0 : Core_models.Marker.Copy Self]
  PRIME (Self) : u32
  MONTY_BITS (Self) : u32
  MONTY_MU (Self) : u32
  MONTY_MASK (Self) :RustM u32 := do
    (Rust_primitives.Hax.cast_op
      (← ((← ((1 : u64) <<<? MONTY_BITS))
        -? (1 : u64))))

attribute [instance] MontyParameters.trait_constr_MontyParameters_i0

--  Convert a u32 into MONTY form.
--  There are no constraints on the input.
--  The output will be a u32 in range `[0, P)`.
def to_monty
    (MP : Type)
    [trait_constr_to_monty_associated_type_i0 : MontyParameters.AssociatedTypes
      MP]
    [trait_constr_to_monty_i0 : MontyParameters MP ]
    (x : u32) :
    RustM u32 := do
  (Rust_primitives.Hax.cast_op
    (← ((← ((← (@Rust_primitives.Hax.cast_op u32 u64 _ x))
        <<<? (MontyParameters.MONTY_BITS MP)))
      %? (← (@Rust_primitives.Hax.cast_op u32 u64 _ (MontyParameters.PRIME MP))))))

--  Montgomery reduction of a value in `0..P << MONTY_BITS`.
-- 
--  The input must be in `[0, MONTY * P)`.
--  The output will be in `[0, P)`.
def monty_reduce
    (MP : Type)
    [trait_constr_monty_reduce_associated_type_i0 :
      MontyParameters.AssociatedTypes
      MP]
    [trait_constr_monty_reduce_i0 : MontyParameters MP ]
    (x : u64) :
    RustM u32 := do
  let t : u64 ←
    ((← (Core_models.Num.Impl_9.wrapping_mul
        x
        (← (Rust_primitives.Hax.cast_op (MontyParameters.MONTY_MU MP)))))
      &&&? (← (Rust_primitives.Hax.cast_op
        (← (MontyParameters.MONTY_MASK MP)))));
  let u : u64 ←
    (t *? (← (@Rust_primitives.Hax.cast_op u32 u64 _ (MontyParameters.PRIME MP))));
  let ⟨x_sub_u, over⟩ ← (Core_models.Num.Impl_9.overflowing_sub x u);
  let x_sub_u_hi : u32 ←
    (Rust_primitives.Hax.cast_op
      (← (x_sub_u >>>? (MontyParameters.MONTY_BITS MP))));
  let corr : u32 ←
    if over then (MontyParameters.PRIME MP) else (pure (0 : u32));
  (Core_models.Num.Impl_8.wrapping_add x_sub_u_hi corr)

--  Convert a u32 out of MONTY form.
--  There are no constraints on the input.
--  The output will be a u32 in range `[0, P)`.
def from_monty
    (MP : Type)
    [trait_constr_from_monty_associated_type_i0 :
      MontyParameters.AssociatedTypes
      MP]
    [trait_constr_from_monty_i0 : MontyParameters MP ]
    (x : u32) :
    RustM u32 := do
  (monty_reduce MP (← (Rust_primitives.Hax.cast_op x)))

--  PackedMontyParameters contains constants needed for MONTY operations for packings of Monty31 fields.
class PackedMontyParameters.AssociatedTypes (Self : Type) where
  [trait_constr_PackedMontyParameters_i0 : MontyParameters.AssociatedTypes Self]

attribute [instance]
  PackedMontyParameters.AssociatedTypes.trait_constr_PackedMontyParameters_i0

class PackedMontyParameters (Self : Type)
  [associatedTypes : outParam (PackedMontyParameters.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr_PackedMontyParameters_i0 : MontyParameters Self]

attribute [instance] PackedMontyParameters.trait_constr_PackedMontyParameters_i0

structure MontyField31
  (MP : Type)
  [trait_constr_MontyField31_associated_type_i0 :
    MontyParameters.AssociatedTypes
    MP]
  [trait_constr_MontyField31_i0 : MontyParameters MP ]
  where
  value : u32
  _phantom : (Core_models.Marker.PhantomData MP)

@[instance] opaque Impl_1.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Clone.Clone.AssociatedTypes
    MP]
  [trait_constr_Impl_1_i0 : Core_models.Clone.Clone MP ]
  [trait_constr_Impl_1_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_1_i1 : MontyParameters MP ] :
  Core_models.Clone.Clone.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (MP : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Clone.Clone.AssociatedTypes
    MP]
  [trait_constr_Impl_1_i0 : Core_models.Clone.Clone MP ]
  [trait_constr_Impl_1_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_1_i1 : MontyParameters MP ] :
  Core_models.Clone.Clone (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_2_associated_type_i0 :
    Core_models.Marker.Copy.AssociatedTypes
    MP]
  [trait_constr_Impl_2_i0 : Core_models.Marker.Copy MP ]
  [trait_constr_Impl_2_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_2_i1 : MontyParameters MP ] :
  Core_models.Marker.Copy.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2
  (MP : Type)
  [trait_constr_Impl_2_associated_type_i0 :
    Core_models.Marker.Copy.AssociatedTypes
    MP]
  [trait_constr_Impl_2_i0 : Core_models.Marker.Copy MP ]
  [trait_constr_Impl_2_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_2_i1 : MontyParameters MP ] :
  Core_models.Marker.Copy (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    Core_models.Default.Default.AssociatedTypes
    MP]
  [trait_constr_Impl_3_i0 : Core_models.Default.Default MP ]
  [trait_constr_Impl_3_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_3_i1 : MontyParameters MP ] :
  Core_models.Default.Default.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3
  (MP : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    Core_models.Default.Default.AssociatedTypes
    MP]
  [trait_constr_Impl_3_i0 : Core_models.Default.Default MP ]
  [trait_constr_Impl_3_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_3_i1 : MontyParameters MP ] :
  Core_models.Default.Default (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_5_associated_type_i0 :
    Core_models.Hash.Hash.AssociatedTypes
    MP]
  [trait_constr_Impl_5_i0 : Core_models.Hash.Hash MP ]
  [trait_constr_Impl_5_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_5_i1 : MontyParameters MP ] :
  Core_models.Hash.Hash.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5
  (MP : Type)
  [trait_constr_Impl_5_associated_type_i0 :
    Core_models.Hash.Hash.AssociatedTypes
    MP]
  [trait_constr_Impl_5_i0 : Core_models.Hash.Hash MP ]
  [trait_constr_Impl_5_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_5_i1 : MontyParameters MP ] :
  Core_models.Hash.Hash (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_6_associated_type_i0 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_6_i0 : MontyParameters MP ] :
  Core_models.Marker.StructuralPartialEq.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6
  (MP : Type)
  [trait_constr_Impl_6_associated_type_i0 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_6_i0 : MontyParameters MP ] :
  Core_models.Marker.StructuralPartialEq (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_7_associated_type_i0 :
    Core_models.Cmp.PartialEq.AssociatedTypes
    MP
    MP]
  [trait_constr_Impl_7_i0 : Core_models.Cmp.PartialEq MP MP ]
  [trait_constr_Impl_7_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_7_i1 : MontyParameters MP ] :
  Core_models.Cmp.PartialEq.AssociatedTypes (MontyField31 MP) (MontyField31 MP)
  :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7
  (MP : Type)
  [trait_constr_Impl_7_associated_type_i0 :
    Core_models.Cmp.PartialEq.AssociatedTypes
    MP
    MP]
  [trait_constr_Impl_7_i0 : Core_models.Cmp.PartialEq MP MP ]
  [trait_constr_Impl_7_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_7_i1 : MontyParameters MP ] :
  Core_models.Cmp.PartialEq (MontyField31 MP) (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes
  (MP : Type)
  [trait_constr_Impl_4_associated_type_i0 : Core_models.Cmp.Eq.AssociatedTypes
    MP]
  [trait_constr_Impl_4_i0 : Core_models.Cmp.Eq MP ]
  [trait_constr_Impl_4_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_4_i1 : MontyParameters MP ] :
  Core_models.Cmp.Eq.AssociatedTypes (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4
  (MP : Type)
  [trait_constr_Impl_4_associated_type_i0 : Core_models.Cmp.Eq.AssociatedTypes
    MP]
  [trait_constr_Impl_4_i0 : Core_models.Cmp.Eq MP ]
  [trait_constr_Impl_4_associated_type_i1 : MontyParameters.AssociatedTypes MP]
  [trait_constr_Impl_4_i1 : MontyParameters MP ] :
  Core_models.Cmp.Eq (MontyField31 MP) :=
  by constructor <;> exact Inhabited.default

--  Create a new field element from any `u32`.
-- 
--  Any `u32` value is accepted and automatically converted to Montgomery form.
def Impl.new
    (MP : Type)
    [trait_constr_new_associated_type_i0 : MontyParameters.AssociatedTypes MP]
    [trait_constr_new_i0 : MontyParameters MP ]
    (value : u32) :
    RustM (MontyField31 MP) := do
  (pure (MontyField31.mk
    (value := (← (to_monty MP value)))
    (_phantom := Core_models.Marker.PhantomData.mk)))

--  FieldParameters contains constants and methods needed to imply PrimeCharacteristicRing, Field and PrimeField32 for MontyField31.
class FieldParameters.AssociatedTypes (Self : Type) where
  [trait_constr_FieldParameters_i0 : PackedMontyParameters.AssociatedTypes Self]

attribute [instance]
  FieldParameters.AssociatedTypes.trait_constr_FieldParameters_i0

class FieldParameters (Self : Type)
  [associatedTypes : outParam (FieldParameters.AssociatedTypes (Self : Type))]
  where
  [trait_constr_FieldParameters_i0 : PackedMontyParameters Self]
  MONTY_ZERO (Self) :RustM (MontyField31 Self) := do (Impl.new Self (0 : u32))
  MONTY_ONE (Self) :RustM (MontyField31 Self) := do (Impl.new Self (1 : u32))
  MONTY_TWO (Self) :RustM (MontyField31 Self) := do (Impl.new Self (2 : u32))
  MONTY_NEG_ONE (Self) :RustM (MontyField31 Self) := do
    (Impl.new Self (← ((MontyParameters.PRIME Self) -? (1 : u32))))
  MONTY_GEN (Self) : (MontyField31 Self)
  HALF_P_PLUS_1 (Self) :RustM u32 := do
    ((← ((MontyParameters.PRIME Self) +? (1 : u32))) >>>? (1 : i32))

attribute [instance] FieldParameters.trait_constr_FieldParameters_i0

--  Create a new field element from something already in MONTY form.
--  This is `pub(crate)` for tests and delayed reduction strategies. If you're using it outside of those, you're
--  likely doing something fishy.
def Impl.new_monty
    (MP : Type)
    [trait_constr_new_monty_associated_type_i0 : MontyParameters.AssociatedTypes
      MP]
    [trait_constr_new_monty_i0 : MontyParameters MP ]
    (value : u32) :
    RustM (MontyField31 MP) := do
  (pure (MontyField31.mk
    (value := value)
    (_phantom := Core_models.Marker.PhantomData.mk)))

--  Produce a u32 in range [0, P) from a field element corresponding to the true value.
def Impl.to_u32
    (MP : Type)
    [trait_constr_to_u32_associated_type_i0 : MontyParameters.AssociatedTypes
      MP]
    [trait_constr_to_u32_i0 : MontyParameters MP ]
    (elem : (MontyField31 MP)) :
    RustM u32 := do
  (from_monty MP (MontyField31.value elem))

--  Convert a `[u32; N]` array to an array of field elements.
-- 
--  Const version of `input.map(MontyField31::new)`.
def Impl.new_array
    (MP : Type)
    (N : usize)
    [trait_constr_new_array_associated_type_i0 : MontyParameters.AssociatedTypes
      MP]
    [trait_constr_new_array_i0 : MontyParameters MP ]
    (input : (RustArray u32 N)) :
    RustM (RustArray (MontyField31 MP) N) := do
  let output : (RustArray (MontyField31 MP) N) ←
    (Rust_primitives.Hax.repeat (← (Impl.new_monty MP (0 : u32))) N);
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
        let output : (RustArray (MontyField31 MP) N) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            output
            i
            (← (Impl.new MP (← input[i]_?))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i output)) :
        RustM
        (Rust_primitives.Hax.Tuple2 usize (RustArray (MontyField31 MP) N)))));
  (pure output)

--  Convert a constant 2d u32 array into a constant 2d array of field elements.
--  Constant version of array.map(MontyField31::new_array).
def Impl.new_2d_array
    (MP : Type)
    (N : usize)
    (M : usize)
    [trait_constr_new_2d_array_associated_type_i0 :
      MontyParameters.AssociatedTypes
      MP]
    [trait_constr_new_2d_array_i0 : MontyParameters MP ]
    (input : (RustArray (RustArray u32 N) M)) :
    RustM (RustArray (RustArray (MontyField31 MP) N) M) := do
  let output : (RustArray (RustArray (MontyField31 MP) N) M) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (← (Impl.new_monty MP (0 : u32))) N))
      M);
  let i : usize := (0 : usize);
  let ⟨i, output⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, output⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, output⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i M) : RustM Bool))
      (fun ⟨i, output⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i output)
      (fun ⟨i, output⟩ =>
        (do
        let output : (RustArray (RustArray (MontyField31 MP) N) M) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            output
            i
            (← (Impl.new_array MP (N) (← input[i]_?))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i output)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (RustArray (RustArray (MontyField31 MP) N) M)))));
  (pure output)

end Mersenne31.Monty_31

