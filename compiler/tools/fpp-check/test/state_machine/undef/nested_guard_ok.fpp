state machine M {
  guard g
  initial enter S
  state S {
    initial enter J
    junction J { if g enter S else enter S }
  }
}