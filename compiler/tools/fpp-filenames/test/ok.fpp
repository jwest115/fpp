port P

array A = [3] U32
constant a = 0
enum E { X, Y }
struct S { x: U32 }
state machine SM1
state machine SM2 {
  initial enter S
  state S
}

type FwOpcodeType
type WithCDefinition = U32
type WithCDefinitionBuiltin = FwOpcodeType
type WithoutCDefinition = A

module M {

  passive component C {
    array A = [3] U32
    constant a = 0
    enum E { X, Y }
    struct S { x: U32 }
  }

}

topology T {
  telemetry packets P {

  }
}
