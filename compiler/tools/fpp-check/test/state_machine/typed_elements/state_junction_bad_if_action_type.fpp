state machine M {
  action a: U32
  guard g
  initial enter S
  state S {
    initial enter J
    junction J { if g do { a } enter T else enter T }
    state T
  }
}