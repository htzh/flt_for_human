import Mathlib.Data.Nat.Basic
namespace Foo
private scoped instance bar : Inhabited Nat := ⟨0⟩
example : Inhabited Nat := inferInstance
end Foo
