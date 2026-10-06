import Mathlib.Data.Nat.Basic
namespace Foo
private def hidden (n : Nat) : Nat := n + 1
def pub (n : Nat) : Nat := hidden n
def pubProp : Prop := hidden 0 = 1
end Foo
