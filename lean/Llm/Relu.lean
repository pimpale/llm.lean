import Mathlib.Algebra.Group.Basic

def relu [Max α] [Zero α] (x : α) : α := max x 0


def relu_backward [BEq α] [Max α] [Zero α] (x dx: α) : α :=
  if relu x == 0 then 0 else dx
