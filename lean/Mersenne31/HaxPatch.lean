import Hax

namespace HaxPatch

def Core_models.Legacy_int_modules.I32.MAX := Int32.maxValue

class overflowing_add (α : Type) where
  oa : α → α → RustM (α × Bool)

@[reducible] instance : overflowing_add Int32 where
  oa := fun (n m : Int32) => RustM.ok (n + m, decide (n > Int32.maxValue - m))

-- We do the `abbrev` ad hoc until type resolution for casting  is robust
/- abbrev Core_models.Num.Impl_2.overflowing_add {α : Type} [self : HaxPatch.overflowing_add α] := @overflowing_add.oa  α self -/

-- We should instead have the above commented-out definition
abbrev Core_models.Num.Impl_2.overflowing_add (n m : Int32) := overflowing_add.oa n m

class overflowing_sub (α : Type) where
  os : α → α → RustM (α × Bool)

abbrev Core_models.Num.Impl_8.overflowing_sub {α : Type} [self : HaxPatch.overflowing_sub α] :=
  @overflowing_sub.os α self

@[reducible] instance : overflowing_sub UInt32 where
  os := fun (n m : UInt32) => RustM.ok (n - m, decide (n < m))

class wrapping_sub (α : Type) where
  ws : α → α → RustM α

abbrev Core_models.Num.Impl_8.wrapping_sub {α : Type} [self : HaxPatch.wrapping_sub α] :=
  @wrapping_sub.ws α self

@[reducible] instance : wrapping_sub UInt32 where
 ws := fun (n m : UInt32) => RustM.ok (n - m)

instance : Cast Bool u32 where
  cast x := ite x 1 0

end HaxPatch
