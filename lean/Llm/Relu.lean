def relu (x : Float):Float:=if x ≥ 0 then x else 0

def relu_backward (x dx: Float) : Float := if x ≥ 0 then dx else 0
